# ADR-010: Store Model and Linear Capability System

## Status
**Proposed**

## Context

The Morph language requires a verified capability-based ownership system. ADR-009 established a phased approach where Phase 1 added `refType` to `Typ` without enforcement, and Phase 2 would add substructural typing. Attempting to add `ref_type` as a `HasType` constructor (ADR-009 Phase 1) failed: it broke preservation because annotating an expression with a capability type doesn't create an actual reference — it's an unsound assertion.

The fundamental insight: **capability typing is not a typing rule — it's a store protocol.** To enforce memory safety, we need:

1. A **store** (heap) carrying typed values at abstract locations
2. **Reference values** pointing into the store
3. **Step rules** that mutate the store (alloc, load, store)
4. **Linear/affine usage tracking** in the typing context
5. **Capability transitions** (iso → val, iso → ref) as type-level operations

The existing `Morph.Memory` module provides a CompCert-style block-offset memory model with `MemByte` (value/undef/poison), `Block` with state tracking, and `Memory` with alloc/free/load/store. This is well-designed but operates at the byte level — too low for the operational semantics. We need a higher-level **typed store** for the Step relation.

## Decision

### 1. Typed Store for Operational Semantics

```lean
-- Abstract location (heap address)
abbrev Loc := Nat

-- Typed store: maps locations to (type, value) pairs
structure Store where
  heap    : Loc → Option (Typ × Value)  -- typed heap contents
  nextLoc : Loc                         -- fresh location generator
  freed   : List Loc                    -- freed locations (for double-free detection)

namespace Store
  def empty : Store := ⟨fun _ => none, 0, []⟩
  
  def alloc (σ : Store) (τ : Typ) (v : Value) : Store × Loc :=
    let loc := σ.nextLoc
    (⟨fun l => if l = loc then some (τ, v) else σ.heap l, loc + 1, σ.freed⟩, loc)
  
  def load (σ : Store) (loc : Loc) : Option (Typ × Value) :=
    σ.heap loc
  
  def store (σ : Store) (loc : Loc) (v : Value) (τ : Typ) : Store :=
    ⟨fun l => if l = loc then some (τ, v) else σ.heap l, σ.nextLoc, σ.freed⟩
  
  def free (σ : Store) (loc : Loc) : Store :=
    ⟨fun l => if l = loc then none else σ.heap l, σ.nextLoc, loc :: σ.freed⟩
end Store
```

### 2. Store-Carrying Step Relation

The `Step` relation changes from `Expr → Expr → Prop` to `Store → Expr → Store → Expr → Prop`:

```lean
inductive Step : Store → Expr → Store → Expr → Prop where
  -- Existing rules carry the store unchanged
  | binop_left (op : Operator) (e1 e1' e2 : Expr) (σ : Store) :
      Step σ e1 σ e1' →
      Step σ (.binop op e1 e2) σ (.binop op e1' e2)
  
  -- New store rules
  | ref_create (σ : Store) (v : Value) (τ : Typ) (cap : Capability) :
      IsValue (.lit v) →
      HasType [] [] (.lit v) τ →
      let (σ', loc) := σ.alloc (.refType cap τ) v;
      Step σ (.refCreate (.lit v) cap τ) σ' (.lit (.loc loc))
  
  | ref_load (σ : Store) (loc : Loc) (τ : Typ) (v : Value) (cap : Capability) :
      σ.heap loc = some (.refType cap τ, v) →
      loc ∉ σ.freed →
      Step σ (.refLoad (.lit (.loc loc))) σ (.lit v)
  
  | ref_store (σ : Store) (loc : Loc) (v : Value) (τ : Typ) (cap : Capability) :
      σ.heap loc = some (.refType cap τ, _) →
      loc ∉ σ.freed →
      cap ≠ .val →  -- cannot store through immutable reference
      Step σ (.refStore (.lit (.loc loc)) (.lit v) τ) (σ.store loc v (.refType cap τ)) (.lit .unit)
  
  | ref_free (σ : Store) (loc : Loc) (τ : Typ) (v : Value) (cap : Capability) :
      σ.heap loc = some (.refType cap τ, v) →
      cap = .iso →  -- only iso (unique owner) can free
      loc ∉ σ.freed →
      Step σ (.refFree (.lit (.loc loc))) (σ.free loc) (.lit .unit)
```

### 3. New Expression and Value Constructors

```lean
-- In Expr:
| refCreate : Expr → Capability → Typ → Expr   -- create reference
| refLoad   : Expr → Expr                       -- dereference
| refStore  : Expr → Expr → Typ → Expr          -- write through reference
| refFree   : Expr → Expr                       -- deallocate (iso only)

-- In Value:
| loc : Loc → Value                              -- location value
```

### 4. Linear Usage Context

```lean
-- Usage tracking for each binding
inductive Usage where
  | zero : Usage   -- not yet used
  | one  : Usage   -- used exactly once
  | many : Usage   -- used multiple times (unrestricted types only)

-- Extended typing context: each binding is (type × usage)
abbrev LinCtx := List (Typ × Usage)

-- A type is unrestricted if it doesn't require linear/affine discipline
def IsUnrestricted : Typ → Bool
  | .refType .iso _ => false   -- iso is linear
  | .refType .val _ => false   -- val is affine  
  | .refType .ref _ => false   -- ref is borrowed
  | _ => true                  -- everything else is unrestricted
```

### 5. Extended HasType with Usage Tracking

```lean
-- The typing judgment now includes a linear context
inductive HasType : LinCtx → TypEnv → Store → Expr → Typ → Prop where
  -- Variable access: consume linear/affine bindings
  | bvar_consume : ∀ ctx Γ σ idx τ u,
      ctx.getD idx (τ, Usage.zero) = (τ, Usage.zero) →
      IsUnrestricted τ = false →
      HasType (ctx.set idx (τ, Usage.one)) Γ σ (.bvar idx) τ
  
  | bvar_copy : ∀ ctx Γ σ idx τ,
      ctx.getD idx (τ, Usage.many) = (τ, Usage.many) →
      IsUnrestricted τ = true →
      HasType ctx Γ σ (.bvar idx) τ
  
  -- Reference creation: consumes the inner value (for iso)
  | ref_create_iso : ∀ ctx Γ σ e v τ,
      HasType ctx Γ σ e τ →
      e = .lit v → IsValue e →
      HasType ctx Γ σ (.refCreate e .iso τ) (.refType .iso τ)
      -- Note: ctx is consumed because iso is linear
  
  -- Reference creation: shares (for val)
  | ref_create_val : ∀ ctx Γ σ e v τ,
      HasType ctx Γ σ e τ →
      e = .lit v → IsValue e →
      HasType ctx Γ σ (.refCreate e .val τ) (.refType .val τ)
  
  -- Reference load: reads without consuming
  | ref_load_type : ∀ ctx Γ σ e loc τ cap,
      HasType ctx Γ σ e (.refType cap τ) →
      σ.heap loc = some (.refType cap τ, _) →
      loc ∉ σ.freed →
      HasType ctx Γ σ (.refLoad e) τ
  
  -- ... other constructors follow the same pattern
```

### 6. Store Typing Invariant

```lean
-- Well-typed store: every allocated location has a consistent type
def StoreTyping (σ : Store) (Γ : TypEnv) : Prop :=
  ∀ loc τ v, σ.heap loc = some (τ, v) →
    loc ∉ σ.freed ∧
    HasType [] Γ σ (.lit v) τ
```

### 7. Soundness with Store

```lean
-- Progress: well-typed ⇒ value or step (with store)
theorem progress_store : ∀ σ e τ,
    HasType [] [] σ e τ →
    StoreTyping σ [] →
    IsValue e ∨ ∃ σ' e', Step σ e σ' e'

-- Preservation: step preserves typing AND store typing
theorem preservation_store : ∀ σ e σ' e' τ,
    HasType [] [] σ e τ →
    StoreTyping σ [] →
    Step σ e σ' e' →
    HasType [] [] σ' e' τ ∧ StoreTyping σ' []
```

### 8. Memory Safety Theorems (Derived from Soundness)

```lean
-- No use-after-free: freed locations cannot be accessed
theorem no_use_after_free : ∀ σ e σ' e' loc τ v,
    Step σ e σ' e' →
    loc ∈ σ.freed →
    e ≠ .refLoad (.lit (.loc loc)) ∧
    e ≠ .refStore (.lit (.loc loc)) _ _

-- No double-free: a location cannot be freed twice
theorem no_double_free : ∀ σ e σ' e' loc,
    Step σ e σ' e' →
    e = .refFree (.lit (.loc loc)) →
    loc ∉ σ.freed

-- Capability transitions are safe: iso→val widens, iso→ref borrows
theorem capability_transition_safe : ∀ σ e σ' e' cap1 cap2 τ,
    Step σ e σ' e' →
    e = .refCreate _ cap1 τ →
    cap2 = .val → cap1 = .iso →  -- widening
    StoreTyping σ' []
```

## Migration Path

### Phase 1: Backward-Compatible Store Introduction (Weeks 1-2)

- Add `Store` type to `Morph/Store.lean`
- Add `Value.loc` constructor to `Core.lean`
- Change `Step` signature to `Store → Expr → Store → Expr → Prop`
- All existing rules carry `σ` unchanged: `Step σ e σ e'`
- Existing soundness proof adapts trivially (store is always empty)

### Phase 2: Reference Operations (Weeks 3-4)

- Add `Expr.refCreate`, `refLoad`, `refStore`, `refFree`
- Add corresponding `Step` constructors
- Add `HasType` constructors for reference operations (WITHOUT linearity)
- Prove store-typed progress and preservation

### Phase 3: Linear Context (Weeks 5-8)

- Add `Usage` and `LinCtx` to `Morph/LinearContext.lean`
- Extend `HasType` to use `LinCtx` instead of plain `bvs`
- Add consumption rules for iso/val types
- Prove linear soundness (affine variables used at most once)

### Phase 4: Memory Safety Proofs (Weeks 9-16)

- Prove `no_use_after_free`
- Prove `no_double_free`
- Prove `capability_transition_safe`
- Prove `acyclicity_theorem` (strong reference graph is a DAG)

### Phase 5: Actor Integration (Weeks 17-20)

- Actor state lives in store with `iso` capability
- Messages deep-copied with `val` capability on send
- Prove actor isolation (state only accessible from owning actor)

## Alternatives Considered

### Option A: Storeless Semantics (Current — REJECTED)

- Cannot prove memory safety properties
- `ref_type` failure demonstrated fundamental unsoundness
- No path to actor isolation proofs

### Option B: Monadic Store (REJECTED)

```lean
def EvalM := StateT Store (ExceptT Panic Identity)
```

- Harder to formalize in Lean (monadic reasoning is more complex)
- Less direct connection to the mathematical model
- Existing proof structure (induction on Step derivation) doesn't apply

### Option C: CompCert-Style Separate Memory (ACCEPTED)

- Reuse existing `Morph.Memory` concepts at a higher level
- Store is a parameter of Step, not embedded in expressions
- Clean separation: expressions describe computation, store describes state
- Proven approach (CompCert does this, 20+ years of verification)

### Option D: Kripke Store (FUTURE — deferred)

- Store typing indexed by a "world" (allocation step)
- Enables reasoning about temporal properties of the store
- Useful for proving liveness (eventual deallocation)
- Deferred to post-v1.0

## Consequences

### Positive

- Memory safety becomes provable (the whole point)
- Actor isolation becomes provable (store contains actor state)
- Walrus operator (`x := e`) unblocked (store mutation)
- Full substructural type theory with mathematical rigor
- Path to information flow proofs (taint via capability tracking)
- Alignment with CompCert methodology (battle-tested approach)

### Negative

- **Every existing proof must be updated.** `Step` signature changes from 2 to 4 parameters. ~800 theorems need adaptation.
- **Proof complexity increases significantly.** Store typing invariant must be maintained across all steps.
- **Linear context adds proof burden.** Usage tracking doubles the complexity of the typing judgment.
- **Migration is non-trivial.** 2 weeks just to update existing proofs to the new `Step` signature.

### Risk Mitigation

- **Incremental migration:** Phase 1 (store parameter) is backward-compatible. Existing rules just carry `σ` unchanged.
- **Automated adaptation:** Most existing proofs can be adapted by inserting `σ` at the right positions. This is mechanical, not creative.
- **Two proof tracks:** Keep old proofs working in a `Morph/Proofs/Storeless/` directory while new proofs are built in `Morph/Proofs/Store/`. Merge when ready.

## Implementation Status (2026-09)

Phases 1a through 1d are complete. The linear-context migration and memory
safety are formalized; **linearity is sound but not yet usable**, which is the
deliberate trade.

### Landed

| Phase | Status | Notes |
|---|---|---|
| 1a — `Step` carries `Store` | done | 74 constructors, store unchanged |
| 1b — store "done" rules | done | `ref_load_done`, `ref_store_done`, `ref_free_done` |
| 1c-α — `HasType` over `LinCtx` | done | `Usage` carried, not enforced |
| 1c-β-1 — context threading | done | `HasType : LinCtx → TypEnv → Expr → Typ → LinCtx → Prop` |
| 1c-β-2 part 1 — consumption | done | `bvar_type` consumes, `binop_*` thread |
| 1d — store typing + safety | done | `HasTypeS`, `progressS`, `preservationS`, 5 `safety_*` theorems |

### The current limitation, stated precisely

`bvar_type` consumes its slot and `bvar_type_many` does not, so usage is
enforced for expressions whose context is threaded. But the binder rules
(`lam_type`, `let_type`, `for_type`, `ArmsTyped.cons`) still require the body to
return *exactly* the context it was given, while a body that consumes returns a
different one. The consequence:

```morph
lam 1 (refFree (bvar 0))    // rejected
```

is **untypeable**. Consuming a linear binding is refused, not silently
accepted. That is the conservative direction: the Phase 1c-α behaviour
(linear programs accepted but unchecked) was unsound, and the current behaviour
is sound-but-incomplete. We would rather reject than trust.

### The remaining piece of 1c-β-2

Three pieces, in dependency order:

1. **Binder rules project.** `lam_type` concludes
   `HasType … cbody → … (cbody.drop paramTys.length)`; `let_type` uses
   `cbody.drop 1`; `for_type` likewise; `ArmsTyped.cons` drops `vars.length`.
   The `drop` machinery (`LinCtx.drop`, `types_drop`, `length_drop`) is in
   place for exactly this.

2. **Consumption-aware substitution.** The missing lemma, stated in the shape
   the semantics demands:
   ```lean
   HasType ((τ1, u1) :: cmid) Γ e2 τ cbody →
   HasType cmid Γ v τ1 →
   HasType cmid Γ (subst' (pfx.length + 1) e2 v) τ (cbody.drop (pfx.length + 1))
   ```
   The `bvar_type` (consuming) branch *replaces* a slot with `v` and so removes
   it from the output context; the `bvar_type_many` branch leaves it. This
   lemma is what `let_subst` and `app_lam` in Preservation need.

   **Why this needs a `pfx`-indexed mutual induction, not a plain one.**
   A naive induction on the derivation of `e2` almost works: for sequencing
   rules the invariant composes, because every sub-term of a derivation from
   `((τ1,u) :: ctx)` is also typed in a context of that shape (`consume` only
   touches slots below the head), so the inductive hypothesis applies and
   `drop 1` lines up. It breaks at **nested binders**. For `e2 = let_ a b` under
   the new rule, `b`'s own output is `Cb.drop 1`, and the induction hypothesis
   yields `b'` typed in `Ca → Cb.drop 1`; but the inner `let_type` needs `b'`
   typed in `((τ1a,u) :: Ca)` and concludes `(Cb.drop 1).drop 1` — one `drop`
   too many. So the hypothesis must be indexed by a prefix, exactly as the
   existing `HasType_subst_depth` is, giving the mutual induction over `pfx`
   and the derivation together. That is a long proof, and it is why several
   attempts at a "small" version of this lemma have stalled.

   **What is already banked.** The `bvar 0` case — the one that makes the
   statement well-posed rather than circular — is proven and committed as
   `HasType_subst_consuming_bvar0`: substituting at exactly the binder position
   yields the value, typed in the body context minus that binder's slot, which
   is the value's own context by `value_does_not_consume`. It closes in one
   line of `cases <;> simp_all`.

3. **Branch merging.** `if_type` and `match` take both branches from the same
   post-condition context and output `LinCtx.merge ct cf`. Note that
   `LinCtx.merge`'s current rule `zero + one = zero` is a syntactic
   approximation and is wrong for path-sensitive checking — expect ADR-013 to
   replace it.

### Why this is acceptable to defer

`value_does_not_consume` is already proven, which is what makes (2)
well-posed: because values never consume, the substituted expression inherits
precisely the context the let-bound value was typed in, which coincides with
the body context minus the binder's slot.

More importantly, ADR-011 places *ownership checking* in the MIR borrow
checker, not in `HasType`, precisely because path sensitivity needs an explicit
CFG. What `HasType` must supply is the discipline we now have: which bindings
are linear, and that each may be consumed at most once. The remaining
substitution lemma is needed for β-reduction under consumption, which the MIR
pipeline performs as a lowering step with its own preservation proof.

## Related Standards

- Memory model spec §2.4: Affine type semantics
- Arc-affine integration spec: ARC + capability interaction
- Memory affine logic spec: Linear/affine type formalism
- Concurrency process algebra spec: Actor isolation requirements
- Execution model spec: Fiber/actor state management
- ISO 26262 §6.7: Memory safety requirements
- DO-178C Level A: Certified software requirements

## Related ADRs

- ADR-008: Walrus deferred (unblocked by this ADR)
- ADR-009: Capability HasType design (superseded by this ADR)
- ADR-006: Complete proof requirement

## Date
2026-06-11

## Author
Nexus (Principal Architect)
