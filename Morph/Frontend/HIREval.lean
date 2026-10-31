/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.HIR
import Morph.Core
import Morph.Syntax
import Morph.Executable
import Morph.Frontend.HIRLower

namespace Morph.Frontend.HIREval

open Morph.Syntax
open Morph.Core
open Morph.Executable
open Morph.Frontend.HIRLower

/-!
# HIR evaluation + lowering preservation (loop 84)

Loop 82 lowered the HIR-representable fragment but left preservation as
named future work: HIR had no evaluator, so there was nothing to preserve
*into*. This module is that evaluator — a fuel-bounded big-step mirror of
`Executable.evalWithFuel` over `HIR.Expr` — plus the first cross-stage
theorem: closed first-order-plus-`let` terms evaluate to the same literal
on both sides (`evalHIR_preservation`).

**Evaluator design.** `HEnv` maps `HIR.Id` to values (first match wins, so
`let` shadowing works). `unop`/`binop` delegate to the *same*
`Executable.evalUnop`/`evalBinop` on the same `Value`, so operator
semantics cannot drift. `whileLoop` consumes one fuel per iteration and
returns `unit` (the surface `forLoop` discipline). `app` is call-by-`Id`:
the function position looks up a `lam`, and parameters bind innermost-first
(mirroring the surface `substAll`-reverse convention). `match` is
first-match-wins over `matchHIRPat`. `infer` is `none` (a placeholder, not
a value). Statement evaluation stays future work — there is no HIR `Stmt`
evaluator yet, so statement preservation waits with it.

**Preservation design.** The proved fragment is `FirstOrder`
(literals, variables, `unop`/`binop`, `let_`, `ifThenElse`, `block`, the
runtime-transparent `field_`/`typeAsc`/`pipe` of loop 85, plus `match_`
over the HIR-representable patterns of loop 86): `lam`/`app` need a
substitution lemma. The environment relation `relEnvAt d` ties surface de
Bruijn context to HIR ids at depth `d` — binder level `k` ↔ `⟨k, "bv"⟩`,
outer slot `m` ↔ `⟨m, "ctx"⟩`, free name `x` ↔ `⟨0, "free:" ++ x⟩` — and is
stable when a `let` pushes (slots do not move, only surface indices do).
`envAllLit` keeps both sides in literal values, since `lam` never appears
in the fragment but *could* appear in the environment.

The proofs recurse structurally on expressions (never on fuel), in the
`liftUnder_zero_eq` mutual style: `fo_eval_is_lit` (every `FirstOrder`
evaluation yields a literal), then the mutual `evalHIR_preservation` /
`evalHIR_preservation_list`. The one non-structural gadget is Option-`mapM`
over the tail-recursive `List.mapM.loop`: `mapM_loop_pointwise` /
`mapM_loop_of_pointwise` characterize it once (accumulator generalized),
and everything else builds on those two.
-/

/-! ## Environment -/

/-- HIR runtime environment: identifier → value. First match wins. -/
abbrev HEnv := List (HIR.Id × HIR.Expr)

/-- Lookup: first match wins. Propositional equality (via the `DecidableEq
HIR.Id` instance) so extension proofs go through `congrArg` instead of
`LawfulBEq`, which `HIR.Id` does not provide. -/
def lookupHEnv : HEnv → HIR.Id → Option HIR.Expr
  | [], _ => none
  | (j, v) :: rest, id => if j = id then some v else lookupHEnv rest id

theorem lookupHEnv_cons_head (id : HIR.Id) (v : HIR.Expr) (env : HEnv) :
    lookupHEnv ((id, v) :: env) id = some v := by
  simp [lookupHEnv]

theorem lookupHEnv_cons_ne {id id' : HIR.Id} {v : HIR.Expr} {env : HEnv}
    (h : ¬ id = id') : lookupHEnv ((id, v) :: env) id' = lookupHEnv env id' := by
  simp [lookupHEnv, h]

/-- Context slots and binder levels live in different namespaces. -/
theorem hirId_ctx_ne_bv {m d : Nat} : ¬ (⟨m, "ctx"⟩ : HIR.Id) = ⟨d, "bv"⟩ := by
  intro h
  have := congrArg HIR.Id.name h
  simp at this

/-- Free names collide with neither namespace (`simp` alone only decides
closed literal equalities, so the open `"free:" ++ x` goes by length). -/
theorem hirId_free_ne_bv {x : String} {d : Nat} :
    ¬ (⟨0, "free:" ++ x⟩ : HIR.Id) = ⟨d, "bv"⟩ := by
  intro h
  have hn := congrArg HIR.Id.name h
  simp only at hn
  have hl : ("free:" ++ x).length = 2 := by
    have hlit : ("bv").length = 2 := by decide
    rw [hn]; exact hlit
  have hlen : ("free:" ++ x).length = "free:".length + x.length := by
    rw [String.length_append]
  have h5 : "free:".length = 5 := by decide
  omega

theorem hirId_free_ne_ctx {x : String} {m : Nat} :
    ¬ (⟨0, "free:" ++ x⟩ : HIR.Id) = ⟨m, "ctx"⟩ := by
  intro h
  have hn := congrArg HIR.Id.name h
  simp only at hn
  have hl : ("free:" ++ x).length = 3 := by
    have hlit : ("ctx").length = 3 := by decide
    rw [hn]; exact hlit
  have hlen : ("free:" ++ x).length = "free:".length + x.length := by
    rw [String.length_append]
  have h5 : "free:".length = 5 := by decide
  omega

/-- Distinct binder levels are distinct ids. -/
theorem hirId_bv_ne {d k : Nat} (h : k ≠ d) :
    ¬ (⟨d, "bv"⟩ : HIR.Id) = ⟨k, "bv"⟩ := by
  intro heq
  exact h (by have := congrArg HIR.Id.index heq; simpa using this.symm)

/-! ## Pattern matching -/

/-- HIR pattern match: `var` binds the value, `wild` binds nothing,
`lit` checks equality. Only values match (the caller evaluates first). -/
def matchHIRPat : HIR.Pattern → HIR.Expr → Option (List HIR.Expr)
  | .wildcard, _ => some []
  | .var _, v => some [v]
  | .lit l, .lit l' => if l == l' then some [] else none
  | .lit _, _ => none

/-! ## The evaluator -/

/-- Fuel-bounded big-step evaluator for HIR, mirroring
`Executable.evalWithFuel` stage by stage. Every recursive call consumes
fuel (blocks map over elements at the predecessor fuel, `whileLoop`
re-enters at the predecessor fuel per iteration), so termination is
structural on fuel — the same shape as the surface evaluator. -/
def evalHIR : Nat → HEnv → HIR.Expr → Option HIR.Expr
  | 0, _, _ => none
  | _fuel + 1, env, .var id => lookupHEnv env id
  | _fuel + 1, _, .lit v => some (.lit v)
  | fuel + 1, env, .unop op e => do
      let v ← evalHIR fuel env e
      match v with
      | .lit u =>
        match Executable.evalUnop op (.lit u) with
        | some (.lit w) => some (.lit w)
        | _ => none
      | _ => none
  | fuel + 1, env, .binop op a b => do
      let va ← evalHIR fuel env a
      let vb ← evalHIR fuel env b
      match va, vb with
      | .lit ua, .lit ub =>
        match Executable.evalBinop op (.lit ua) (.lit ub) with
        | some (.lit w) => some (.lit w)
        | _ => none
      | _, _ => none
  | _fuel + 1, _, .lam params body => some (.lam params body)
  | fuel + 1, env, .app fid args => do
      let fn ← lookupHEnv env fid
      match fn with
      | .lam params body =>
        if args.length ≠ params.length then none
        else do
          let argv ← args.mapM (evalHIR fuel env)
          let n := params.length
          let binds := (List.range n).filterMap fun j =>
            match params[j]?, argv[n - 1 - j]? with
            | some p, some v => some (p, v)
            | _, _ => none
          if binds.length ≠ n then none
          else evalHIR fuel (binds ++ env) body
      | _ => none
  | fuel + 1, env, .let id init body => do
      let v ← evalHIR fuel env init
      evalHIR fuel ((id, v) :: env) body
  | fuel + 1, env, .ifThenElse c t f => do
      let cv ← evalHIR fuel env c
      match cv with
      | .lit (.bool true) => evalHIR fuel env t
      | .lit (.bool false) => evalHIR fuel env f
      | _ => none
  | fuel + 1, env, .whileLoop c body => do
      let cv ← evalHIR fuel env c
      match cv with
      | .lit (.bool true) => do
        let _ ← body.mapM (evalHIR fuel env)
        evalHIR fuel env (.whileLoop c body)
      | .lit (.bool false) => some (.lit .unit)
      | _ => none
  | fuel + 1, env, .match scrut arms => do
      let sv ← evalHIR fuel env scrut
      match arms with
      | [] => none
      | (pat, body) :: rest =>
        match matchHIRPat pat sv, pat with
        | some [], _ => evalHIR fuel env body
        | some [v], .var id => evalHIR fuel ((id, v) :: env) body
        | _, _ => evalHIR fuel env (.match sv rest)
  | fuel + 1, env, .block es => do
      let vs ← es.mapM (evalHIR fuel env)
      match vs with
      | [] => some (.lit .unit)
      | _ => some vs.getLast!
  | _, _, .infer => none

/-! ## Small gadgets -/

/-- Destructure a successful `Option.bind`. -/
theorem bind_some_eq {m : Option α} {g : α → Option β} {y : β}
    (h : m.bind g = some y) : ∃ a, m = some a ∧ g a = some y := by
  cases m with
  | none => simp [Option.bind] at h
  | some a => exact ⟨a, rfl, by simpa [Option.bind] using h⟩

/-- `evalUnop` only ever produces literals. -/
theorem evalUnop_is_lit {op : Operator} {a v : Syntax.Expr}
    (h : Executable.evalUnop op a = some v) : ∃ w, v = .lit w := by
  unfold Executable.evalUnop at h
  split at h <;> (first | contradiction |
    (have h2 := Option.some.inj h; subst h2; exact ⟨_, rfl⟩))

/-- `evalBinop` only ever produces literals (the nested op-match needs a
second round of splitting; kept as separate `all_goals` passes since a
`split`-under-`first` nesting loses the closing tactic). -/
theorem evalBinop_is_lit {op : Operator} {a b v : Syntax.Expr}
    (h : Executable.evalBinop op a b = some v) : ∃ w, v = .lit w := by
  unfold Executable.evalBinop at h
  split at h
  all_goals (try split at h)
  all_goals (first | contradiction |
    (have h2 := Option.some.inj h; subst h2; exact ⟨_, rfl⟩))

/-- Empty contexts look up nothing. -/
theorem getBv?_empty (n : Nat) : Context.empty.getBv? n = none := by rfl

theorem getFv?_empty (x : String) : Context.empty.getFv? x = none := by rfl

/-- Pushing exposes the new value at index 0 and shifts the rest. -/
theorem getBv?_pushBv_zero (ctx : Context) (v : Syntax.Expr) :
    (ctx.pushBv v).getBv? 0 = some v := by rfl

theorem getBv?_pushBv_succ (ctx : Context) (v : Syntax.Expr) (n : Nat) :
    (ctx.pushBv v).getBv? (n + 1) = ctx.getBv? n := by rfl

/-- Pushing never touches free variables. -/
theorem getFv?_pushBv (ctx : Context) (v : Syntax.Expr) (x : String) :
    (ctx.pushBv v).getFv? x = ctx.getFv? x := by rfl

/-- Mapping `getLast!` over a nonempty list. -/
theorem map_getLast! {l : List α} (hne : l ≠ []) (f : α → β) [Inhabited β] :
    (l.map f).getLast! = f (l.getLast hne) := by
  induction l with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs => exact ih (by simp)

/-! ## Environment relations -/

/-- Every entry of a surface context is a literal. The fragment never
evaluates a `lam` to a non-literal, but environments *could* hold one;
this rules that out wherever preservation applies. -/
def envAllLit (ctx : Context) : Prop :=
  (∀ n v, ctx.getBv? n = some v → ∃ w, v = .lit w) ∧
  (∀ x v, ctx.getFv? x = some v → ∃ w, v = .lit w)

/-- Surface de Bruijn context ↔ HIR ids at depth `d`: binder level `k`
(`k < d`) is `⟨k, "bv"⟩`, outer slot `m` (`n = m + d`) is `⟨m, "ctx"⟩`,
free names map to `⟨0, "free:" ++ x⟩`. -/
def relEnvAt (d : Nat) (ctx : Context) (henv : HEnv) : Prop :=
  (∀ n w, d ≤ n → ctx.getBv? n = some (.lit w) →
    lookupHEnv henv ⟨n - d, "ctx"⟩ = some (.lit w))
  ∧ (∀ k w, k < d → ctx.getBv? (d - 1 - k) = some (.lit w) →
    lookupHEnv henv ⟨k, "bv"⟩ = some (.lit w))
  ∧ (∀ x w, ctx.getFv? x = some (.lit w) →
    lookupHEnv henv ⟨0, "free:" ++ x⟩ = some (.lit w))

/-- The empty environment relation holds trivially. -/
theorem relEnvAt_empty (d : Nat) : relEnvAt d Context.empty [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro n w _ h
    rw [getBv?_empty] at h
    cases h
  · intro k w _ h
    rw [getBv?_empty] at h
    cases h
  · intro x w h
    rw [getFv?_empty] at h
    cases h

/-- Pushing a literal preserves literalness. -/
theorem envAllLit_pushBv {ctx : Context} {v : Syntax.Expr} {w : Value}
    (hlit : envAllLit ctx) (hv : v = .lit w) : envAllLit (ctx.pushBv v) := by
  refine ⟨?_, ?_⟩
  · intro n v' h
    cases n with
    | zero =>
      rw [getBv?_pushBv_zero] at h
      have hvv : v = v' := Option.some.inj h
      subst hvv
      exact ⟨w, hv⟩
    | succ m =>
      rw [getBv?_pushBv_succ] at h
      exact hlit.1 m v' h
  · intro x v' h
    rw [getFv?_pushBv] at h
    exact hlit.2 x v' h

/-- Extending both sides (surface push ↔ HIR cons of the depth-`d` binder)
preserves the relation: slots do not move, only surface indices shift. -/
theorem relEnvAt_pushBv {d : Nat} {ctx : Context} {henv : HEnv}
    {v : Syntax.Expr} {w : Value}
    (hrel : relEnvAt d ctx henv) (hv : v = .lit w) :
    relEnvAt (d + 1) (ctx.pushBv v) ((⟨d, "bv"⟩, .lit w) :: henv) := by
  refine ⟨?_, ?_, ?_⟩
  · -- outer slots: index `n = m + 1`, slot `m` is untouched
    intro n w' hn hget
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [getBv?_pushBv_succ] at hget
    have hm : d ≤ m := by omega
    have hfound := hrel.1 m w' hm hget
    have heq : m - d = (m + 1) - (d + 1) := by omega
    rw [← heq]
    exact lookupHEnv_cons_ne (fun heq => hirId_ctx_ne_bv heq.symm) |>.trans hfound
    -- note: `⟨d,"bv"⟩ = ⟨m-d,"ctx"⟩` is impossible by name; `heq.symm`
    -- orients it for `hirId_ctx_ne_bv`
  · -- binder levels: level `d` is the new value, levels below shift by one
    intro k w' hk hget
    by_cases hkd : k = d
    · rw [hkd] at hk hget ⊢
      have h0 : d + 1 - 1 - d = 0 := by omega
      rw [h0, getBv?_pushBv_zero] at hget
      have hv' : v = .lit w' := Option.some.inj hget
      rw [hv] at hv'
      cases hv'
      exact lookupHEnv_cons_head _ _ _
    · have hkd' : k < d := by omega
      have hidx : d + 1 - 1 - k = (d - 1 - k) + 1 := by omega
      rw [hidx, getBv?_pushBv_succ] at hget
      have hfound := hrel.2.1 k w' hkd' hget
      have hne : ¬ (⟨d, "bv"⟩ : HIR.Id) = ⟨k, "bv"⟩ := by
        intro heq
        have hi := congrArg HIR.Id.index heq
        simp only at hi
        omega
      exact (lookupHEnv_cons_ne hne).trans hfound
  · -- free names: pushing never touches them
    intro x w' hget
    rw [getFv?_pushBv] at hget
    have hfound := hrel.2.2 x w' hget
    exact (lookupHEnv_cons_ne (fun heq => hirId_free_ne_bv heq.symm)).trans hfound

/-! ## The tail-recursive `mapM` gadget -/

/-- `mapM.loop` equations, by definitional unfolding. -/
theorem mapM_loop_nil (f : α → Option β) (bs : List β) :
    List.mapM.loop f [] bs = some bs.reverse := rfl

theorem mapM_loop_cons (f : α → Option β) (a : α) (as : List α) (bs : List β) :
    List.mapM.loop f (a :: as) bs =
      (f a).bind (fun v => List.mapM.loop f as (v :: bs)) := rfl

theorem mapM_eq_loop (f : α → Option β) (xs : List α) :
    xs.mapM f = List.mapM.loop f xs [] := rfl

/-- Forward: a successful loop run pins every element's result. The
accumulator stays general, so both `mapM` (`bs = []`) and cons-cells
follow. -/
theorem mapM_loop_pointwise : ∀ (xs : List α) (bs : List β) (ys : List β)
    (f : α → Option β),
    List.mapM.loop f xs bs = some ys →
    ∃ zs, xs.length = zs.length ∧
      (∀ (i : Nat) x, xs[i]? = some x → ∃ y, zs[i]? = some y ∧ f x = some y) ∧
      ys = bs.reverse ++ zs
  | [], bs, ys, f => by
    intro h
    rw [mapM_loop_nil] at h
    have h2 := Option.some.inj h
    subst h2
    exact ⟨[], rfl, fun i x hx => by simp at hx, by simp⟩
  | a :: as, bs, ys, f => by
    intro h
    rw [mapM_loop_cons] at h
    obtain ⟨v, hva, htl⟩ := bind_some_eq h
    obtain ⟨zs, hlen, hpt, hys⟩ := mapM_loop_pointwise as (v :: bs) ys f htl
    refine ⟨v :: zs, by simp [hlen], ?_, ?_⟩
    · intro i x hx
      cases i with
      | zero =>
        simp at hx
        obtain rfl := hx
        exact ⟨v, by simp, hva⟩
      | succ i =>
        simp at hx
        obtain ⟨y, hy, hfy⟩ := hpt i x hx
        exact ⟨y, by simpa using hy, hfy⟩
    · rw [hys]
      simp

/-- Converse: pointwise successes run the loop. -/
theorem mapM_loop_of_pointwise : ∀ (xs : List α) (bs : List β) (zs : List β)
    (f : α → Option β),
    xs.length = zs.length →
    (∀ (i : Nat) x, xs[i]? = some x → ∃ y, zs[i]? = some y ∧ f x = some y) →
    List.mapM.loop f xs bs = some (bs.reverse ++ zs)
  | [], bs, zs, f => by
    intro hlen _
    cases zs with
    | nil =>
      rw [mapM_loop_nil]
      simp
    | cons z zs' => simp at hlen
  | a :: as, bs, zs, f => by
    intro hlen hpt
    obtain ⟨z, zs', rfl⟩ : ∃ z zs', zs = z :: zs' := by
      cases zs with
      | nil => simp at hlen
      | cons z zs' => exact ⟨z, zs', rfl⟩
    obtain ⟨y, hy, hfy⟩ := hpt 0 a (by simp)
    simp at hy
    obtain rfl := hy
    have has : as.length = zs'.length := by simpa using hlen
    have hpt' : ∀ (i : Nat) x, as[i]? = some x → ∃ y, zs'[i]? = some y ∧ f x = some y := by
      intro i x hx
      obtain ⟨y, hy, hfy⟩ := hpt (i + 1) x (by simpa using hx)
      exact ⟨y, by simpa using hy, hfy⟩
    have ih := mapM_loop_of_pointwise as (z :: bs) zs' f has hpt'
    rw [mapM_loop_cons, hfy]
    simpa using ih

/-- Cons builds on success. -/
theorem mapM_cons_some {f : α → Option β} {a : α} {as : List α}
    {y : β} {ys' : List β}
    (ha : f a = some y) (ht : as.mapM f = some ys') :
    (a :: as).mapM f = some (y :: ys') := by
  rw [mapM_eq_loop, mapM_loop_cons, ha]
  simp only [Option.bind_some]
  obtain ⟨zs, hlen, hpt, hys⟩ :=
    mapM_loop_pointwise as [] ys' f (by rwa [← mapM_eq_loop])
  simp at hys
  subst hys
  have h := mapM_loop_of_pointwise as [y] _ f hlen hpt
  simpa using h

/-- Cons destructures on success. -/
theorem mapM_cons_destr {f : α → Option β} {a : α} {as : List α}
    {ys : List β}
    (h : (a :: as).mapM f = some ys) :
    ∃ y ys', f a = some y ∧ as.mapM f = some ys' ∧ ys = y :: ys' := by
  rw [mapM_eq_loop, mapM_loop_cons] at h
  obtain ⟨y, hfy, htl⟩ := bind_some_eq h
  obtain ⟨zs, hlen, hpt, hys⟩ := mapM_loop_pointwise as [y] _ f htl
  refine ⟨y, zs, hfy, ?_, ?_⟩
  · rw [mapM_eq_loop]
    have h2 := mapM_loop_of_pointwise as [] zs f hlen hpt
    simpa using h2
  · simpa using hys

/-! ## Application functions evaluate to `lam` -/

/-- A successful application evaluated its function to a `lam` (loop 85:
the `pipe` case needs this — a `FirstOrder` function position can only
evaluate to a literal, so a succeeding pipe is impossible). -/
theorem app_eval_fn (fuel : Nat) (ctx : Context) (f : Syntax.Expr)
    (args : List Syntax.Expr) (r : Syntax.Expr) :
    evalWithFuel (fuel + 1) ctx (.app f args) = some r →
    ∃ n body, evalWithFuel fuel ctx f = some (.lam n body) := by
  intro h
  simp only [evalWithFuel] at h
  obtain ⟨fnVal, hfn, hrest⟩ := bind_some_eq h
  cases fnVal with
  | lam n body => exact ⟨n, body, hfn⟩
  | bvar n => simp at hrest
  | fvar x => simp at hrest
  | lit v => simp at hrest
  | unop op e => simp at hrest
  | binop op a b => simp at hrest
  | app fn args => simp at hrest
  | let_ a b => simp at hrest
  | ifThenElse c t e => simp at hrest
  | forLoop s e b => simp at hrest
  | block es => simp at hrest
  | match_ s arms => simp at hrest
  | field_ a n => simp at hrest
  | pipe a g => simp at hrest
  | typeAsc a t => simp at hrest
  | some_ a => simp at hrest
  | none_ => simp at hrest
  | ok_ a => simp at hrest
  | err_ a => simp at hrest
  | nullCoalesce a b => simp at hrest
  | tuple_ es => simp at hrest
  | arrayLit es => simp at hrest
  | arrayIndex a i => simp at hrest
  | refCreate e c t => simp at hrest
  | refLoad e => simp at hrest
  | refStore e v t => simp at hrest
  | refFree e => simp at hrest
  | refCast e t => simp at hrest

/-! ## `FirstOrder` evaluations yield literals -/

mutual

/-- Every element of a successful `FirstOrder` block evaluation is a literal. -/
theorem fo_list_is_lit : ∀ (fuel : Nat) (ctx : Context)
    (es : List Syntax.Expr) (vs : List Syntax.Expr),
    (∀ e ∈ es, FirstOrder e) → envAllLit ctx →
    es.mapM (evalWithFuel fuel ctx) = some vs →
    ∃ wvs : List Value, vs = wvs.map .lit
  | _, _, [], _ => by
    intro _ _ h
    rw [mapM_eq_loop, mapM_loop_nil] at h
    have h2 := Option.some.inj h
    subst h2
    exact ⟨[], rfl⟩
  | fuel, ctx, e :: es, _ => by
    intro hfo hlit hmap
    obtain ⟨v, vs', hvv, hvs', rfl⟩ := mapM_cons_destr hmap
    obtain ⟨w, rfl⟩ := fo_eval_is_lit fuel ctx e v (hfo e (by simp)) hlit hvv
    obtain ⟨wvs, rfl⟩ := fo_list_is_lit fuel ctx es vs'
      (fun e' he' => hfo e' (by simp [he'])) hlit hvs'
    exact ⟨w :: wvs, rfl⟩

/-- A successful `FirstOrder` arms-dispatch yields a literal. Structural on
the arms list (fuel stays fixed throughout); the `none` branch recurses on
the tail, the hit branches delegate to `fo_eval_is_lit` on the arm body.
The hypothesis is the already-dispatched arms-match at `fuel` — no fuel
unfolding is needed anywhere, since `matchPat` is not fuel-indexed. -/
theorem fo_match_arms_is_lit : ∀ (fuel : Nat) (ctx : Context) (w : Value)
    (arms : List (Syntax.Pattern × Syntax.Expr)) (v : Syntax.Expr),
    (∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ arms →
      p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x)) →
    (∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ arms →
      FirstOrder b) → envAllLit ctx →
    (match arms with
     | [] => (none : Option Syntax.Expr)
     | (pat, body) :: rest => match matchPat pat (.lit w) with
       | some vs => evalWithFuel fuel (ctx.pushBvs vs) body
       | none => evalWithFuel fuel ctx (.match_ (.lit w) rest)) = some v →
    ∃ u, v = .lit u
  | _, _, _, [], _ => by
    intro hpat_ok hfo_all hlit h
    simp at h
  | fuel, ctx, w, (pat, body) :: rest, _ => by
    intro hpat_ok hfo_all hlit h
    have hmem : (pat, body) ∈ (pat, body) :: rest := by simp
    have hpat := hpat_ok _ _ hmem
    have hb := hfo_all _ _ hmem
    have hpat_rest : ∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ rest →
        p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x) :=
      fun p b hm => hpat_ok _ _ (List.mem_cons_of_mem _ hm)
    have hfo_rest : ∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ rest →
        FirstOrder b :=
      fun p b hm => hfo_all _ _ (List.mem_cons_of_mem _ hm)
    cases hpat with
    | inl hw =>
      subst hw
      simp only [matchPat] at h
      have hbody : evalWithFuel fuel ctx body = some _ := h
      exact fo_eval_is_lit fuel ctx body _ hb hlit hbody
    | inr h =>
      cases h with
      | inl hl =>
        obtain ⟨l, rfl⟩ := hl
        simp only [matchPat] at h
        by_cases heq : l == w
        · simp [heq] at h
          have hbody : evalWithFuel fuel ctx body = some _ := h
          exact fo_eval_is_lit fuel ctx body _ hb hlit hbody
        · simp [heq] at h
          -- h : the `none` branch — a tail `.match_` eval at variable
          -- `fuel`. Re-expose its dispatch by casing fuel (concrete
          -- zero/succ unfold definitionally). No recursion happens under
          -- the casing, so the mutual structural discipline is unaffected.
          cases fuel with
          | zero => simp [evalWithFuel] at h
          | succ f =>
            simp only [evalWithFuel] at h
            obtain ⟨sv2, hsv2, harms2⟩ := bind_some_eq h
            have hsv2_eq : sv2 = .lit w := by
              cases f with
              | zero => simp [evalWithFuel] at hsv2
              | succ f' =>
                simp only [evalWithFuel] at hsv2
                exact (Option.some.inj hsv2).symm
            subst hsv2_eq
            exact fo_match_arms_is_lit f ctx w rest _ hpat_rest hfo_rest hlit harms2
      | inr hr =>
        obtain ⟨x, rfl⟩ := hr
        simp only [matchPat] at h
        have hbody : evalWithFuel fuel (ctx.pushBv (.lit w)) body = some _ := h
        exact fo_eval_is_lit fuel (ctx.pushBv (.lit w)) body _ hb
          (envAllLit_pushBv hlit rfl) hbody

/-- A successful `FirstOrder` evaluation yields a literal. Structural on
the `FirstOrder` derivation (fuel stays fixed throughout). -/
theorem fo_eval_is_lit : ∀ (fuel : Nat) (ctx : Context)
    (e : Syntax.Expr) (v : Syntax.Expr),
    FirstOrder e → envAllLit ctx →
    evalWithFuel fuel ctx e = some v → ∃ w, v = .lit w
  | 0, _, _, _ => by
    intro hfo hlit h
    simp [evalWithFuel] at h
  | fuel + 1, ctx, _, _ => by
    intro hfo hlit h
    cases hfo with
    | lit l =>
      simp only [evalWithFuel] at h
      have h2 := Option.some.inj h
      subst h2
      exact ⟨_, rfl⟩
    | bvar n =>
      simp only [evalWithFuel] at h
      exact hlit.1 n _ h
    | fvar x =>
      simp only [evalWithFuel] at h
      exact hlit.2 x _ h
    | unop op a ha =>
      simp only [evalWithFuel] at h
      obtain ⟨va, hva, hop⟩ := bind_some_eq h
      obtain ⟨u, rfl⟩ := fo_eval_is_lit fuel ctx a va ha hlit hva
      exact evalUnop_is_lit hop
    | binop op a b ha hb =>
      simp only [evalWithFuel] at h
      obtain ⟨va, hva, hrest⟩ := bind_some_eq h
      obtain ⟨vb, hvb, hop⟩ := bind_some_eq hrest
      obtain ⟨ua, rfl⟩ := fo_eval_is_lit fuel ctx a va ha hlit hva
      obtain ⟨ub, rfl⟩ := fo_eval_is_lit fuel ctx b vb hb hlit hvb
      exact evalBinop_is_lit hop
    | let_ init body hi hb =>
      simp only [evalWithFuel] at h
      obtain ⟨v1, hv1, hbody⟩ := bind_some_eq h
      obtain ⟨w1, rfl⟩ := fo_eval_is_lit fuel ctx init v1 hi hlit hv1
      exact fo_eval_is_lit fuel (ctx.pushBv (.lit w1)) body _ hb
        (envAllLit_pushBv hlit rfl) hbody
    | ifThenElse c t f hc ht hf =>
      simp only [evalWithFuel] at h
      obtain ⟨cv, hcv, hbr⟩ := bind_some_eq h
      obtain ⟨u, rfl⟩ := fo_eval_is_lit fuel ctx c cv hc hlit hcv
      cases u with
      | bool b =>
        cases b with
        | true =>
          simp only at hbr
          exact fo_eval_is_lit fuel ctx t _ ht hlit hbr
        | false =>
          simp only at hbr
          exact fo_eval_is_lit fuel ctx f _ hf hlit hbr
      | int _ | string _ | pointer _ | float _ | unit | undef
      | some _ | none | ok _ | err _ | tuple_ _ | array_ _ | loc _
      | closure _ _ =>
        simp at hbr
    | block es hall =>
      simp only [evalWithFuel] at h
      obtain ⟨vs, hvs, hlast⟩ := bind_some_eq h
      obtain ⟨wvs, rfl⟩ := fo_list_is_lit fuel ctx es vs hall hlit hvs
      cases wvs with
      | nil =>
        simp at hlast
        exact ⟨.unit, hlast.symm⟩
      | cons w ws =>
        simp only [List.map_cons] at hlast
        rw [← List.map_cons, map_getLast! (by simp) (Syntax.Expr.lit)] at hlast
        have h2 := Option.some.inj hlast
        subst h2
        exact ⟨_, rfl⟩
    | field_ e _ he =>
      simp only [evalWithFuel] at h
      exact fo_eval_is_lit fuel ctx e _ he hlit h
    | typeAsc e _ he =>
      simp only [evalWithFuel] at h
      exact fo_eval_is_lit fuel ctx e _ he hlit h
    | pipe a f ha hf =>
      simp only [evalWithFuel] at h
      obtain ⟨va, hva, happ⟩ := bind_some_eq h
      obtain ⟨u, rfl⟩ := fo_eval_is_lit fuel ctx a va ha hlit hva
      cases fuel with
      | zero => simp [evalWithFuel] at happ
      | succ fuel =>
        obtain ⟨n, body, hfn⟩ := app_eval_fn fuel ctx f [.lit u] _ happ
        obtain ⟨uf, heq⟩ := fo_eval_is_lit fuel ctx f _ hf hlit hfn
        simp at heq
    | match_ scrut arms hscr hpat_ok hfo_all =>
      simp only [evalWithFuel] at h
      obtain ⟨sv, hsv, harms⟩ := bind_some_eq h
      obtain ⟨w, rfl⟩ := fo_eval_is_lit fuel ctx scrut sv hscr hlit hsv
      exact fo_match_arms_is_lit fuel ctx w arms _ hpat_ok hfo_all hlit harms

end

/-! ## Fuel monotonicity -/

/-- Lifting a successful `mapM` run to the next fuel level. -/
theorem evalHIR_mapM_mono (fuel : Nat) (henv : HEnv)
    (lift : ∀ (e' : HIR.Expr) (v : HIR.Expr),
      evalHIR fuel henv e' = some v → evalHIR (fuel + 1) henv e' = some v)
    (es : List HIR.Expr) (vs : List HIR.Expr) :
    es.mapM (evalHIR fuel henv) = some vs →
    es.mapM (evalHIR (fuel + 1) henv) = some vs := by
  induction es generalizing vs with
  | nil =>
    intro h
    exact h
  | cons a as ih =>
    intro h
    obtain ⟨y, ys', ha, ht, rfl⟩ := mapM_cons_destr h
    exact mapM_cons_some (lift _ _ ha) (ih _ ht)

/-- Success is stable under extra fuel (loop 85): the transparent
lowering cases (`field_`/`typeAsc`) leave the HIR side untouched, so the
predecessor-fuel induction hypothesis must be lifted one level. -/
theorem evalHIR_mono : ∀ (fuel : Nat) (henv : HEnv) (e' : HIR.Expr)
    (v : HIR.Expr),
    evalHIR fuel henv e' = some v → evalHIR (fuel + 1) henv e' = some v := by
  intro fuel
  induction fuel with
  | zero =>
    intro henv e' v h
    simp [evalHIR] at h
  | succ fuel ih =>
    intro henv e' v h
    have mlift := evalHIR_mapM_mono fuel henv (fun e' v hv => ih henv e' v hv)
    cases e' with
    | var id =>
      simp only [evalHIR] at h ⊢
      exact h
    | lit l =>
      simp only [evalHIR] at h ⊢
      exact h
    | unop op a =>
      simp only [evalHIR] at h ⊢
      obtain ⟨x, hxa, hop⟩ := bind_some_eq h
      rw [ih henv a x hxa]
      exact hop
    | binop op a b =>
      simp only [evalHIR] at h ⊢
      obtain ⟨xa, hxa, hrest⟩ := bind_some_eq h
      obtain ⟨xb, hxb, hop⟩ := bind_some_eq hrest
      rw [ih henv a xa hxa, ih henv b xb hxb]
      exact hop
    | lam params body =>
      simp only [evalHIR] at h ⊢
      exact h
    | app fid args =>
      simp only [evalHIR] at h ⊢
      obtain ⟨fn, hfn, hrest⟩ := bind_some_eq h
      cases fn with
      | lam params body =>
        have hlen : args.length = params.length := by
          by_cases hc : args.length = params.length
          · exact hc
          · simp [hc] at hrest
        simp [hlen] at hrest
        obtain ⟨argv, hargv, hrest2⟩ := bind_some_eq hrest
        have hargv' := mlift _ _ hargv
        have hrest3 : (if (List.filterMap (fun j => match params[j]?, argv[params.length - 1 - j]? with | some p, some v => some (p, v) | _, _ => none) (List.range params.length)).length = params.length then evalHIR fuel (List.filterMap (fun j => match params[j]?, argv[params.length - 1 - j]? with | some p, some v => some (p, v) | _, _ => none) (List.range params.length) ++ henv) body else none) = some v := hrest2
        have hlen2 : (List.filterMap (fun j => match params[j]?, argv[params.length - 1 - j]? with | some p, some v => some (p, v) | _, _ => none) (List.range params.length)).length = params.length := by
          by_cases hc : (List.filterMap (fun j => match params[j]?, argv[params.length - 1 - j]? with | some p, some v => some (p, v) | _, _ => none) (List.range params.length)).length = params.length
          · exact hc
          · simp [hc] at hrest3
        simp [hlen2] at hrest3
        have hrec' := ih _ _ v hrest3
        simp [hfn, hargv', hrec', hlen, hlen2]
      | var id => simp at hrest
      | lit l => simp at hrest
      | unop op e => simp at hrest
      | binop op a b => simp at hrest
      | app f a => simp at hrest
      | «let» i b => simp at hrest
      | ifThenElse c t f => simp at hrest
      | whileLoop c b => simp at hrest
      | «match» s a => simp at hrest
      | block es => simp at hrest
      | infer => simp at hrest
    | «let» id init body =>
      simp only [evalHIR] at h ⊢
      obtain ⟨v1, hv1, hbody⟩ := bind_some_eq h
      have hv1' := ih henv init v1 hv1
      have hbody' := ih ((id, v1) :: henv) body v hbody
      simp [hv1', hbody']
    | ifThenElse c t f =>
      simp only [evalHIR] at h ⊢
      obtain ⟨cv, hcv, hrest⟩ := bind_some_eq h
      have hcv' := ih henv c cv hcv
      cases cv with
      | lit u =>
        cases u with
        | bool b =>
          cases b with
          | true =>
            simp only at hrest
            have hbr' := ih henv t v hrest
            simp [hcv', hbr']
          | false =>
            simp only at hrest
            have hbr' := ih henv f v hrest
            simp [hcv', hbr']
        | int _ => simp at hrest
        | string _ => simp at hrest
        | float _ => simp at hrest
        | unit => simp at hrest
        | undef => simp at hrest
        | none => simp at hrest
        | some _ => simp at hrest
        | ok _ => simp at hrest
        | err _ => simp at hrest
        | tuple_ _ => simp at hrest
        | array_ _ => simp at hrest
        | loc _ => simp at hrest
        | pointer _ => simp at hrest
        | closure _ _ => simp at hrest
      | var id => simp at hrest
      | unop op e => simp at hrest
      | binop op a b => simp at hrest
      | app f a => simp at hrest
      | lam p b => simp at hrest
      | «let» i b => simp at hrest
      | ifThenElse c t f => simp at hrest
      | whileLoop c b => simp at hrest
      | «match» s a => simp at hrest
      | block es => simp at hrest
      | infer => simp at hrest
    | whileLoop c body =>
      simp only [evalHIR] at h
      rw [evalHIR.eq_10]
      obtain ⟨cv, hcv, hrest⟩ := bind_some_eq h
      have hcv' := ih henv c cv hcv
      cases cv with
      | lit u =>
        cases u with
        | bool b =>
          cases b with
          | true =>
            simp only at hrest
            obtain ⟨loopRes, hmap, hrec⟩ := bind_some_eq hrest
            have hmap' := mlift _ _ hmap
            have hrec' := ih henv (.whileLoop c body) v hrec
            simp [hcv', hmap', hrec']
          | false =>
            simp only at hrest
            simp [hcv', hrest]
        | int _ => simp at hrest
        | string _ => simp at hrest
        | float _ => simp at hrest
        | unit => simp at hrest
        | undef => simp at hrest
        | none => simp at hrest
        | some _ => simp at hrest
        | ok _ => simp at hrest
        | err _ => simp at hrest
        | tuple_ _ => simp at hrest
        | array_ _ => simp at hrest
        | loc _ => simp at hrest
        | pointer _ => simp at hrest
        | closure _ _ => simp at hrest
      | var id => simp at hrest
      | unop op e => simp at hrest
      | binop op a b => simp at hrest
      | app f a => simp at hrest
      | lam p b => simp at hrest
      | «let» i b => simp at hrest
      | ifThenElse c t f => simp at hrest
      | whileLoop c b => simp at hrest
      | «match» s a => simp at hrest
      | block es => simp at hrest
      | infer => simp at hrest
    | «match» scrut arms =>
      simp only [evalHIR] at h
      rw [evalHIR.eq_11]
      obtain ⟨sv, hscrut, hrest⟩ := bind_some_eq h
      have hscrut' := ih henv scrut sv hscrut
      cases arms with
      | nil => simp at hrest
      | cons pr rest =>
        obtain ⟨pat, body⟩ := pr
        cases hmp : matchHIRPat pat sv with
        | none =>
          simp [hmp] at hrest
          have hrec' := ih henv (.match sv rest) v hrest
          simp [hscrut', hmp, hrec']
        | some vs =>
          cases vs with
          | nil =>
            simp [hmp] at hrest
            have hrec' := ih henv body v hrest
            simp [hscrut', hmp, hrec']
          | cons v' vs' =>
            cases vs' with
            | nil =>
              cases pat with
              | var id =>
                simp [hmp] at hrest
                have hrec' := ih ((id, v') :: henv) body v hrest
                simp [hscrut', hmp, hrec']
              | lit l =>
                simp [hmp] at hrest
                have hrec' := ih henv (.match sv rest) v hrest
                simp [hscrut', hmp, hrec']
              | wildcard =>
                simp [hmp] at hrest
                have hrec' := ih henv (.match sv rest) v hrest
                simp [hscrut', hmp, hrec']
            | cons v'' vs'' =>
              simp [hmp] at hrest
              have hrec' := ih henv (.match sv rest) v hrest
              simp [hscrut', hmp, hrec']
    | block es =>
      simp only [evalHIR] at h ⊢
      obtain ⟨loopRes, hmap, hlast⟩ := bind_some_eq h
      have hmap' := mlift _ _ hmap
      cases loopRes with
      | nil =>
        simp at hlast
        simp [hmap', hlast]
      | cons x xs =>
        simp at hlast
        simp [hmap', hlast]
    | infer =>
      simp [evalHIR] at h

/-! ## Lowering preservation -/

/-- List preservation from single preservation at a fixed fuel.
Induction on the expression list: the head uses `single_at`, the tail
uses the list IH (same fuel — list elements evaluate at the same fuel
as the list itself). -/
theorem evalHIR_list_of_single (fuel : Nat)
    (single_at : ∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (e : Syntax.Expr) (e' : HIR.Expr) (w : Value),
      FirstOrder e → toHIRAt d e = some e' →
      relEnvAt d ctx henv → envAllLit ctx →
      evalWithFuel fuel ctx e = some (.lit w) →
      evalHIR fuel henv e' = some (.lit w))
    : ∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (es : List Syntax.Expr) (es' : List HIR.Expr),
      (∀ e ∈ es, FirstOrder e) → toHIRListAt d es = some es' →
      relEnvAt d ctx henv → envAllLit ctx →
      ∀ (vs : List Syntax.Expr),
      es.mapM (evalWithFuel fuel ctx) = some vs →
      ∃ wvs : List Value, vs = wvs.map .lit ∧
        es'.mapM (evalHIR fuel henv) = some (wvs.map .lit) := by
  intro d ctx henv es
  induction es with
  | nil =>
    intro es' hfo hlower hrel hlit vs hmap
    simp only [toHIRListAt] at hlower
    have h2 := Option.some.inj hlower
    subst h2
    rw [mapM_eq_loop, mapM_loop_nil] at hmap
    have h4 := Option.some.inj hmap
    subst h4
    exact ⟨[], rfl, by simp [mapM_eq_loop, mapM_loop_nil]⟩
  | cons e es ih =>
    intro es' hfo hlower hrel hlit vs hmap
    have hhead : FirstOrder e := hfo e (by simp)
    have htail : ∀ e' ∈ es, FirstOrder e' :=
      fun e' he' => hfo e' (by simp [he'])
    have hsub : ∃ (e' : HIR.Expr) (es'' : List HIR.Expr),
        toHIRAt d e = some e' ∧ toHIRListAt d es = some es'' ∧
        (e' :: es'') = es' := by
      cases h1 : toHIRAt d e with
      | none =>
        cases h2 : toHIRListAt d es with
        | none =>
          simp only [toHIRListAt, h1, h2] at hlower
          cases hlower
        | some _ =>
          simp only [toHIRListAt, h1, h2] at hlower
          cases hlower
      | some e' =>
        cases h2 : toHIRListAt d es with
        | none =>
          simp only [toHIRListAt, h1, h2] at hlower
          cases hlower
        | some es'' =>
          simp only [toHIRListAt, h1, h2] at hlower
          exact ⟨e', es'', rfl, rfl, Option.some.inj hlower⟩
    obtain ⟨e', es'', he', hes'', rfl⟩ := hsub
    obtain ⟨v, vs', hvv, hvs', rfl⟩ := mapM_cons_destr hmap
    obtain ⟨w, rfl⟩ := fo_eval_is_lit fuel ctx e v hhead hlit hvv
    have h_ih_head := single_at d ctx henv e e' w hhead he' hrel hlit hvv
    obtain ⟨wvs, rfl, htailH⟩ := ih es'' htail hes'' hrel hlit vs' hvs'
    exact ⟨w :: wvs, rfl, mapM_cons_some h_ih_head htailH⟩

/-- Arms preservation at a fixed fuel, from single preservation at the same
fuel. The surface dispatch and the HIR dispatch both run their bodies at
`fuel` — the dispatch itself consumes no fuel on either side (the enclosing
match node already paid one level) — so `single_at` applies directly to
hit bodies; a miss tail is just another `FirstOrder` match expression at
the same fuel. Stated in dispatch form so the caller can rewrite after
unfolding one match level on each side. -/
theorem evalHIR_arms_preservation (fuel : Nat)
    (single_at : ∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (e : Syntax.Expr) (e' : HIR.Expr) (w : Value),
      FirstOrder e → toHIRAt d e = some e' →
      relEnvAt d ctx henv → envAllLit ctx →
      evalWithFuel fuel ctx e = some (.lit w) →
      evalHIR fuel henv e' = some (.lit w))
    : ∀ (d : Nat) (ctx : Context) (henv : HEnv) (w : Value)
      (arms : List (Syntax.Pattern × Syntax.Expr))
      (arms' : List (HIR.Pattern × HIR.Expr)) (w' : Value),
      toHIRArmsAt d arms = some arms' →
      (∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ arms →
        p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x)) →
      (∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ arms →
        FirstOrder b) →
      relEnvAt d ctx henv → envAllLit ctx →
      (match arms with
       | [] => (none : Option Syntax.Expr)
       | (pat, body) :: rest => match matchPat pat (.lit w) with
         | some vs => evalWithFuel fuel (ctx.pushBvs vs) body
         | none => evalWithFuel fuel ctx (.match_ (.lit w) rest)) = some (.lit w') →
      (match arms' with
       | [] => (none : Option HIR.Expr)
       | (pat, body) :: rest => match matchHIRPat pat (.lit w), pat with
         | some [], _ => evalHIR fuel henv body
         | some [v], .var id => evalHIR fuel ((id, v) :: henv) body
         | _, _ => evalHIR fuel henv (.match (.lit w) rest)) = some (.lit w') := by
  intro d ctx henv w arms
  cases arms with
  | nil =>
    intro arms' w' hlower _ _ _ _ h
    simp only [toHIRArmsAt] at hlower
    have h2 := Option.some.inj hlower
    subst h2
    simp at h
  | cons hd rest =>
    obtain ⟨pat, body⟩ := hd
    intro arms' w' hlower hpat_ok hfo_all hrel hlit h
    have hsub : ∃ (pat' : HIR.Pattern) (body' : HIR.Expr)
        (rest' : List (HIR.Pattern × HIR.Expr)),
        toHIRPatAt d pat = some pat' ∧
        toHIRAt (d + patBindCount pat) body = some body' ∧
        toHIRArmsAt d rest = some rest' ∧
        ((pat', body') :: rest') = arms' := by
      cases h1 : toHIRPatAt d pat with
      | none =>
        cases h2 : toHIRAt (d + patBindCount pat) body with
        | none =>
          cases h3 : toHIRArmsAt d rest with
          | none =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            cases hlower
          | some _ =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            cases hlower
        | some _ =>
          cases h3 : toHIRArmsAt d rest with
          | none =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            cases hlower
          | some _ =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            cases hlower
      | some pat' =>
        cases h2 : toHIRAt (d + patBindCount pat) body with
        | none =>
          cases h3 : toHIRArmsAt d rest with
          | none =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            cases hlower
          | some _ =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            cases hlower
        | some body' =>
          cases h3 : toHIRArmsAt d rest with
          | none =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            cases hlower
          | some rest' =>
            simp only [toHIRArmsAt, h1, h2, h3] at hlower
            exact ⟨pat', body', rest', rfl, rfl, rfl, Option.some.inj hlower⟩
    obtain ⟨pat', body', rest', hpat', hbody', hrest', rfl⟩ := hsub
    have hmem : (pat, body) ∈ (pat, body) :: rest := by simp
    have hpat := hpat_ok _ _ hmem
    have hbody_fo := hfo_all _ _ hmem
    have hpat_rest : ∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ rest →
        p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x) :=
      fun p b hm => hpat_ok _ _ (List.mem_cons_of_mem _ hm)
    have hfo_rest : ∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ rest →
        FirstOrder b :=
      fun p b hm => hfo_all _ _ (List.mem_cons_of_mem _ hm)
    cases hpat with
    | inl hw =>
      subst hw
      have hpeq : pat' = .wildcard :=
        (Option.some.inj (by simpa [toHIRPatAt] using hpat')).symm
      subst hpeq
      simp only [patBindCount, Nat.add_zero] at hbody'
      simp only [matchPat] at h
      have hpush : ctx.pushBvs [] = ctx := rfl
      rw [hpush] at h
      have hH := single_at d ctx henv body body' w' hbody_fo hbody' hrel hlit h
      simpa [matchHIRPat] using hH
    | inr h =>
      cases h with
      | inl hl =>
        obtain ⟨l, rfl⟩ := hl
        have hpeq : pat' = .lit l :=
          (Option.some.inj (by simpa [toHIRPatAt] using hpat')).symm
        subst hpeq
        simp only [patBindCount, Nat.add_zero] at hbody'
        simp only [matchPat] at h
        by_cases heq : l == w
        · simp [heq] at h
          have hpush : ctx.pushBvs [] = ctx := rfl
          rw [hpush] at h
          have hH := single_at d ctx henv body body' w' hbody_fo hbody' hrel hlit h
          simpa [matchHIRPat, heq] using hH
        · simp [heq] at h
          have hFO : FirstOrder (.match_ (.lit w) rest) :=
            .match_ _ _ (.lit _) hpat_rest hfo_rest
          have hlow : toHIRAt d (.match_ (.lit w) rest) =
              some (.match (.lit w) rest') := by
            simp only [toHIRAt, hrest']
          have hH := single_at d ctx henv _ _ w' hFO hlow hrel hlit h
          simpa [matchHIRPat, heq] using hH
      | inr hr =>
        obtain ⟨x, rfl⟩ := hr
        have hpeq : pat' = .var ⟨d, "bv"⟩ := by
          have h2 : HIR.Pattern.var ⟨d, "bv"⟩ = pat' := by
            simpa [toHIRPatAt] using hpat'
          exact h2.symm
        subst hpeq
        simp only [patBindCount] at hbody'
        simp only [matchPat] at h
        have hpush : ctx.pushBvs [.lit w] = ctx.pushBv (.lit w) := rfl
        rw [hpush] at h
        have hrel' := relEnvAt_pushBv hrel (v := .lit w) rfl
        have hlit' := envAllLit_pushBv hlit (v := .lit w) (w := w) rfl
        have hH := single_at (d + 1) (ctx.pushBv (.lit w))
          ((⟨d, "bv"⟩, .lit w) :: henv) body body' w'
          hbody_fo hbody' hrel' hlit' h
        simpa [matchHIRPat] using hH

/-- Single preservation at `fuel + 1` from both halves at `fuel`.
Every recursive evaluation is at the predecessor fuel, so the induction
hypotheses apply; the block case uses the list half at `fuel`. -/
theorem evalHIR_single_succ (fuel : Nat)
    (ih_single : ∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (e : Syntax.Expr) (e' : HIR.Expr) (w : Value),
      FirstOrder e → toHIRAt d e = some e' →
      relEnvAt d ctx henv → envAllLit ctx →
      evalWithFuel fuel ctx e = some (.lit w) →
      evalHIR fuel henv e' = some (.lit w))
    (ih_list : ∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (es : List Syntax.Expr) (es' : List HIR.Expr),
      (∀ e ∈ es, FirstOrder e) → toHIRListAt d es = some es' →
      relEnvAt d ctx henv → envAllLit ctx →
      ∀ (vs : List Syntax.Expr),
      es.mapM (evalWithFuel fuel ctx) = some vs →
      ∃ wvs : List Value, vs = wvs.map .lit ∧
        es'.mapM (evalHIR fuel henv) = some (wvs.map .lit))
    : ∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (e : Syntax.Expr) (e' : HIR.Expr) (w : Value),
      FirstOrder e → toHIRAt d e = some e' →
      relEnvAt d ctx henv → envAllLit ctx →
      evalWithFuel (fuel + 1) ctx e = some (.lit w) →
      evalHIR (fuel + 1) henv e' = some (.lit w) := by
  intro d ctx henv e e' w hfo hlower hrel hlit heval
  cases hfo with
  | lit v =>
    simp only [toHIRAt] at hlower
    have h2 := Option.some.inj hlower
    subst h2
    simp only [evalWithFuel] at heval
    have h3 := Option.some.inj heval
    cases h3
    simp only [evalHIR]
  | bvar n =>
    simp only [evalWithFuel] at heval
    by_cases h : n < d
    · rw [toHIRAt_bvar_bound d n h] at hlower
      have h2 := Option.some.inj hlower
      subst h2
      simp only [evalHIR]
      have hk : d - 1 - n < d := by omega
      have hidx : d - 1 - (d - 1 - n) = n := by omega
      have heval' : ctx.getBv? (d - 1 - (d - 1 - n)) = some (.lit w) := by
        rw [hidx]; exact heval
      exact hrel.2.1 (d - 1 - n) w hk heval'
    · rw [toHIRAt_bvar_outer d n h] at hlower
      have h2 := Option.some.inj hlower
      subst h2
      simp only [evalHIR]
      exact hrel.1 n w (by omega) heval
  | fvar x =>
    simp only [evalWithFuel] at heval
    simp only [toHIRAt] at hlower
    have h2 := Option.some.inj hlower
    subst h2
    simp only [evalHIR]
    exact hrel.2.2 x w heval
  | unop op a ha =>
    have hsub : ∃ (a' : HIR.Expr), toHIRAt d a = some a' ∧
        (.unop op a' : HIR.Expr) = e' := by
      cases h1 : toHIRAt d a with
      | none =>
        simp only [toHIRAt, h1, Option.map] at hlower
        cases hlower
      | some a' =>
        simp only [toHIRAt, h1, Option.map] at hlower
        exact ⟨a', rfl, Option.some.inj hlower⟩
    obtain ⟨a', ha', rfl⟩ := hsub
    simp only [evalWithFuel] at heval
    obtain ⟨va, hva, hop⟩ := bind_some_eq heval
    obtain ⟨u, rfl⟩ := fo_eval_is_lit fuel ctx a va ha hlit hva
    have h_ih := ih_single d ctx henv a a' u ha ha' hrel hlit hva
    simp [evalHIR, h_ih, hop]
  | binop op a b ha hb =>
    have hsub : ∃ (a' b' : HIR.Expr), toHIRAt d a = some a' ∧
        toHIRAt d b = some b' ∧ (.binop op a' b' : HIR.Expr) = e' := by
      cases h1 : toHIRAt d a with
      | none =>
        cases h2 : toHIRAt d b with
        | none =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
        | some _ =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
      | some a' =>
        cases h2 : toHIRAt d b with
        | none =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
        | some b' =>
          simp only [toHIRAt, h1, h2] at hlower
          exact ⟨a', b', rfl, rfl, Option.some.inj hlower⟩
    obtain ⟨a', b', ha', hb', rfl⟩ := hsub
    simp only [evalWithFuel] at heval
    obtain ⟨va, hva, hrest⟩ := bind_some_eq heval
    obtain ⟨vb, hvb, hop⟩ := bind_some_eq hrest
    obtain ⟨ua, rfl⟩ := fo_eval_is_lit fuel ctx a va ha hlit hva
    obtain ⟨ub, rfl⟩ := fo_eval_is_lit fuel ctx b vb hb hlit hvb
    have h_ih_a := ih_single d ctx henv a a' ua ha ha' hrel hlit hva
    have h_ih_b := ih_single d ctx henv b b' ub hb hb' hrel hlit hvb
    simp [evalHIR, h_ih_a, h_ih_b, hop]
  | let_ init body hi hb =>
    have hsub : ∃ (init' body' : HIR.Expr), toHIRAt d init = some init' ∧
        toHIRAt (d + 1) body = some body' ∧
        (.let ⟨d, "bv"⟩ init' body' : HIR.Expr) = e' := by
      cases h1 : toHIRAt d init with
      | none =>
        cases h2 : toHIRAt (d + 1) body with
        | none =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
        | some _ =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
      | some init' =>
        cases h2 : toHIRAt (d + 1) body with
        | none =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
        | some body' =>
          simp only [toHIRAt, h1, h2] at hlower
          exact ⟨init', body', rfl, rfl, Option.some.inj hlower⟩
    obtain ⟨init', body', hi', hb', rfl⟩ := hsub
    simp only [evalWithFuel] at heval
    obtain ⟨v1, hv1, hbody⟩ := bind_some_eq heval
    obtain ⟨w1, rfl⟩ := fo_eval_is_lit fuel ctx init v1 hi hlit hv1
    have h_ih_init := ih_single d ctx henv init init' w1 hi hi' hrel hlit hv1
    have hrel' := relEnvAt_pushBv hrel (v := .lit w1) rfl
    have hlit' := envAllLit_pushBv hlit (v := .lit w1) (w := w1) rfl
    have h_ih_body := ih_single (d + 1) (ctx.pushBv (.lit w1))
      ((⟨d, "bv"⟩, .lit w1) :: henv) body body' w hb hb' hrel' hlit' hbody
    simp [evalHIR, h_ih_init, h_ih_body]
  | ifThenElse c t f hc ht hf =>
    have hsub : ∃ (c' t' f' : HIR.Expr), toHIRAt d c = some c' ∧
        toHIRAt d t = some t' ∧ toHIRAt d f = some f' ∧
        (.ifThenElse c' t' f' : HIR.Expr) = e' := by
      cases h1 : toHIRAt d c with
      | none =>
        cases h2 : toHIRAt d t with
        | none =>
          cases h3 : toHIRAt d f with
          | none =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            cases hlower
          | some _ =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            cases hlower
        | some _ =>
          cases h3 : toHIRAt d f with
          | none =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            cases hlower
          | some _ =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            cases hlower
      | some c' =>
        cases h2 : toHIRAt d t with
        | none =>
          cases h3 : toHIRAt d f with
          | none =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            cases hlower
          | some _ =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            cases hlower
        | some t' =>
          cases h3 : toHIRAt d f with
          | none =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            cases hlower
          | some f' =>
            simp only [toHIRAt, h1, h2, h3] at hlower
            exact ⟨c', t', f', rfl, rfl, rfl, Option.some.inj hlower⟩
    obtain ⟨c', t', f', hc', ht', hf', rfl⟩ := hsub
    simp only [evalWithFuel] at heval
    obtain ⟨cv, hcv, hbr⟩ := bind_some_eq heval
    obtain ⟨u, rfl⟩ := fo_eval_is_lit fuel ctx c cv hc hlit hcv
    have hcond := ih_single d ctx henv c c' u hc hc' hrel hlit hcv
    cases u with
    | bool b =>
      cases b with
      | true =>
        simp only at hbr
        have h_ih := ih_single d ctx henv t t' w ht ht' hrel hlit hbr
        simp [evalHIR, hcond, h_ih]
      | false =>
        simp only at hbr
        have h_ih := ih_single d ctx henv f f' w hf hf' hrel hlit hbr
        simp [evalHIR, hcond, h_ih]
    | int _ | string _ | pointer _ | float _ | unit | undef
    | some _ | none | ok _ | err _ | tuple_ _ | array_ _ | loc _
    | closure _ _ =>
      simp at hbr
  | block es hall =>
    have hsub : ∃ (es_list' : List HIR.Expr),
        toHIRListAt d es = some es_list' ∧
        (.block es_list' : HIR.Expr) = e' := by
      cases h1 : toHIRListAt d es with
      | none =>
        simp only [toHIRAt, h1, Option.map] at hlower
        cases hlower
      | some es_list' =>
        simp only [toHIRAt, h1, Option.map] at hlower
        exact ⟨es_list', rfl, Option.some.inj hlower⟩
    obtain ⟨es_list', hs', rfl⟩ := hsub
    simp only [evalWithFuel] at heval
    obtain ⟨vs, hvs, hlast⟩ := bind_some_eq heval
    obtain ⟨wvs, rfl, hvsH⟩ :=
      ih_list d ctx henv es es_list' hall hs' hrel hlit vs hvs
    cases wvs with
    | nil =>
      simp at hlast
      have hw : Value.unit = w := hlast
      subst hw
      simp [evalHIR, hvsH]
    | cons w0 ws =>
      simp only [List.map_cons] at hlast
      rw [← List.map_cons, map_getLast! (by simp) (Syntax.Expr.lit)] at hlast
      have h3 := Option.some.inj hlast
      have hw : (w0 :: ws).getLast (by simp) = w := by cases h3; rfl
      subst hw
      simp [evalHIR, hvsH]
      show (HIR.Expr.lit w0 :: List.map HIR.Expr.lit ws).getLast! = _
      rw [← List.map_cons, map_getLast! (by simp) (HIR.Expr.lit)]
  | field_ e name he =>
    -- `field_` is runtime-erased: both sides just evaluate the receiver.
    simp only [toHIRAt] at hlower
    simp only [evalWithFuel] at heval
    have hfuel := ih_single d ctx henv e e' w he hlower hrel hlit heval
    exact evalHIR_mono fuel henv e' _ hfuel
  | typeAsc e τ he =>
    simp only [toHIRAt] at hlower
    simp only [evalWithFuel] at heval
    have hfuel := ih_single d ctx henv e e' w he hlower hrel hlit heval
    exact evalHIR_mono fuel henv e' _ hfuel
  | pipe a f ha hf =>
    -- The surface evaluates `a |> f` by applying `f`; a succeeding pipe
    -- forces `f` to a `lam`, contradicting `FirstOrder f` (always a literal).
    simp only [evalWithFuel] at heval
    obtain ⟨va, hva, happ⟩ := bind_some_eq heval
    obtain ⟨u, rfl⟩ := fo_eval_is_lit fuel ctx a va ha hlit hva
    cases fuel with
    | zero => simp [evalWithFuel] at happ
    | succ fuel =>
      obtain ⟨n, body, hfn⟩ := app_eval_fn fuel ctx f [.lit u] _ happ
      obtain ⟨uf, heq⟩ := fo_eval_is_lit fuel ctx f _ hf hlit hfn
      simp at heq
  | match_ scrut arms hscr hpat_ok hfo_all =>
    have hsub : ∃ (scrut' : HIR.Expr) (arms_list' : List (HIR.Pattern × HIR.Expr)),
        toHIRAt d scrut = some scrut' ∧
        toHIRArmsAt d arms = some arms_list' ∧
        (.match scrut' arms_list' : HIR.Expr) = e' := by
      cases h1 : toHIRAt d scrut with
      | none =>
        cases h2 : toHIRArmsAt d arms with
        | none =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
        | some _ =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
      | some scrut' =>
        cases h2 : toHIRArmsAt d arms with
        | none =>
          simp only [toHIRAt, h1, h2] at hlower
          cases hlower
        | some arms_list' =>
          simp only [toHIRAt, h1, h2] at hlower
          exact ⟨scrut', arms_list', rfl, rfl, Option.some.inj hlower⟩
    obtain ⟨scrut', arms_list', hscr', harms', rfl⟩ := hsub
    simp only [evalWithFuel] at heval
    obtain ⟨sv, hsv, harms⟩ := bind_some_eq heval
    obtain ⟨w0, rfl⟩ := fo_eval_is_lit fuel ctx scrut sv hscr hlit hsv
    have hcond := ih_single d ctx henv scrut scrut' w0 hscr hscr' hrel hlit hsv
    have hH := evalHIR_arms_preservation fuel ih_single d ctx henv w0
      arms arms_list' w harms' hpat_ok hfo_all hrel hlit harms
    simp only [evalHIR] at ⊢
    rw [hcond] at ⊢
    exact hH

/-- Fuel induction core: single-expression and list preservation together.
Every recursive evaluation is at the predecessor fuel, so Nat induction
applies; the list half at each fuel follows elementwise from the single
half at the same fuel, and blocks use the list half at the predecessor. -/
theorem evalHIR_preservation_both : ∀ (fuel : Nat),
    (∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (e : Syntax.Expr) (e' : HIR.Expr) (w : Value),
      FirstOrder e → toHIRAt d e = some e' →
      relEnvAt d ctx henv → envAllLit ctx →
      evalWithFuel fuel ctx e = some (.lit w) →
      evalHIR fuel henv e' = some (.lit w))
    ∧ (∀ (d : Nat) (ctx : Context) (henv : HEnv)
      (es : List Syntax.Expr) (es' : List HIR.Expr),
      (∀ e ∈ es, FirstOrder e) → toHIRListAt d es = some es' →
      relEnvAt d ctx henv → envAllLit ctx →
      ∀ (vs : List Syntax.Expr),
      es.mapM (evalWithFuel fuel ctx) = some vs →
      ∃ wvs : List Value, vs = wvs.map .lit ∧
        es'.mapM (evalHIR fuel henv) = some (wvs.map .lit)) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro d ctx henv e e' w hfo hlower hrel hlit heval
      simp [evalWithFuel] at heval
    · intro d ctx henv es es' hfo hlower hrel hlit vs hmap
      cases es with
      | nil =>
        simp only [toHIRListAt] at hlower
        have h2 := Option.some.inj hlower
        subst h2
        rw [mapM_eq_loop, mapM_loop_nil] at hmap
        have h4 := Option.some.inj hmap
        subst h4
        exact ⟨[], rfl, by simp [mapM_eq_loop, mapM_loop_nil]⟩
      | cons e es =>
        obtain ⟨v, vs', hvv, hvs', rfl⟩ := mapM_cons_destr hmap
        simp [evalWithFuel] at hvv
  | succ fuel ih =>
    obtain ⟨ih_s, ih_l⟩ := ih
    have s_succ := evalHIR_single_succ fuel ih_s ih_l
    exact ⟨s_succ, evalHIR_list_of_single (fuel + 1) s_succ⟩

/-- List version: successful evaluations correspond elementwise (as
literals), so block results agree. -/
theorem evalHIR_preservation_list : ∀ (fuel : Nat) (d : Nat)
    (ctx : Context) (henv : HEnv)
    (es : List Syntax.Expr) (es' : List HIR.Expr),
    (∀ e ∈ es, FirstOrder e) → toHIRListAt d es = some es' →
    relEnvAt d ctx henv → envAllLit ctx →
    ∀ (vs : List Syntax.Expr),
    es.mapM (evalWithFuel fuel ctx) = some vs →
    ∃ wvs : List Value, vs = wvs.map .lit ∧
      es'.mapM (evalHIR fuel henv) = some (wvs.map .lit) :=
  fun fuel d ctx henv es es' hfo hlower hrel hlit vs hmap =>
    (evalHIR_preservation_both fuel).2 d ctx henv es es' hfo hlower hrel hlit vs hmap

/-- The first cross-stage theorem: closed first-order-plus-`let` terms
evaluate to the same literal on both sides. -/
theorem evalHIR_preservation : ∀ (fuel : Nat) (d : Nat)
    (ctx : Context) (henv : HEnv)
    (e : Syntax.Expr) (e' : HIR.Expr) (w : Value),
    FirstOrder e → toHIRAt d e = some e' →
    relEnvAt d ctx henv → envAllLit ctx →
    evalWithFuel fuel ctx e = some (.lit w) →
    evalHIR fuel henv e' = some (.lit w) :=
  fun fuel d ctx henv e e' w hfo hlower hrel hlit heval =>
    (evalHIR_preservation_both fuel).1 d ctx henv e e' w hfo hlower hrel hlit heval

end Morph.Frontend.HIREval
