# Stage B scope — verified MIR→CLIF lowering for straight-line code

Status: scoping note, loop 144 (2026-11-06). Design record only — no Stage B
code is in the tree. Governed by
`.specs/02_adrs/ADR-032-backend-selection-cranelift-verified-lowering.md`
(Cranelift, verified lowering) and `docs/STAGEA-PREP-125.md` §1 (D-4 strict
subset). Moves no gates: G-1, G-3, G-7 stay open per `HARD-GATES.md`.

## 0. What Stage B inherits, and where it attaches

Stage A closed in loop 143. `compile_total`
(`Morph/HIRToMIRTotal.lean`) ends at

```
execFunc 2 func ⟨fun _ => none, store⟩ = some w
```

so the proved chain stops at **MIR execution**. Stage B's job is the next
arrow, and it attaches exactly there — Stage B takes a MIR run as its
hypothesis, never a source program. Composed with `compile_total`, the
user-facing statement becomes source-run-implies-CLIF-run without Stage B ever
mentioning HIR:

```
surface → HIR → MIR → CLIF        (proved: compile_total ∘ clif_correct)
CLIF → machine code               (trusted: Cranelift)
```

Two Stage A facts Stage B depends on and must not restate:

- `StraightStmts 256 ss` is the fragment gate, already needed by
  `compile_total`; Stage B reuses it rather than inventing a second one.
- `compile_total` is one-directional. Stage B inherits that discipline: it
  claims "MIR produced `w` ⇒ CLIF produces `w`", never "CLIF trapped ⇒ MIR
  stalled".

## 1. Measured semantic gaps (the substance of this note)

ADR-032 chose the backend and the proof interface. It did not compare the two
value domains, and the comparison is where Stage B's real work is. All four
facts below were measured in this tree, not assumed.

### 1.1 `Value.int` is unbounded; CLIF integers are fixed-width

`Morph/Core.lean:120` — `Value.int : Int`, arbitrary precision.
`Morph/Executable.lean:81-83` — `add`/`sub`/`mul` are `Int` arithmetic with no
wrap and no overflow condition. `Instr.binop` carries a `τ : Typ`, but the MIR
oracle ignores it (`evalBinOp` receives no type).

CLIF `i64`/`i32` arithmetic wraps (and `sadd_overflow`-style ops exist, but the
plain ones wrap). So `2147483647 + 1` at i32, or any `i64` overflow, is a
*value* in MIR and a *wrapped value* in CLIF. **MIR→CLIF is therefore not
value-preserving in general.** Stage B's theorem must carry a representability
hypothesis, and it must cover intermediate values, not only the result (§4).

### 1.2 Division semantics differ in two independent ways

Measured with `#eval` against this toolchain:

| expression | Lean `Int` | CLIF `sdiv`/`srem` |
| --- | --- | --- |
| `(-7) / 2` | `-4` | `-3` (truncating) |
| `(-7) % 2` | `1` | `-1` (truncating) |
| `7 / (-2)` | `-3` | `-3` |
| `7 % (-2)` | `1` | `1` |
| `x / 0`, `x % 0` | `0` (`Executable.lean:84-85`) | **trap** |

Lean's `Int` uses the Euclidean pair: the remainder is always non-negative.
Cranelift's `sdiv`/`srem` truncate toward zero. These agree only when the
operands are non-negative — i.e. exactly the cases a differential corpus of
positive literals would cover, which is why this is worth writing down.

The zero case is worse than a mismatch in convention: MIR *defines* `x/0 = 0`
and CLIF traps. A lowering that emitted `sdiv` directly would turn a defined
MIR result into a machine trap.

**Decision: `div` and `mod` are out of the Stage B subset.** The path back in
is a guarded Euclidean sequence (`sdiv` + `srem` + a sign correction for the
non-negative remainder, plus an explicit zero-divisor branch that yields `0`),
with a lemma that it recovers the Euclidean pair. That is a bounded piece of
work and a natural Stage-B2 item; it is not in B1.

### 1.3 Shifts are unbounded in Lean and width-bounded in CLIF

`Operator.shl`/`shr` on `Int` shift by any amount; CLIF shifts are defined for
amounts `< 64` and mask or trap otherwise. So shifts need their own amount
hypothesis in addition to §1.1's range hypothesis (`0 ≤ n < 64`).

### 1.4 Non-scalar values have no Stage B encoding

`Value.string`, `.float`, `.pointer`, `.tuple_`, `.array_`, `.closure`,
`.some`/`.none`/`.ok`/`.err`, `.undef` all appear in `Value` and therefore can
appear as `Instr.const` payloads. None has a CLIF encoding at this stage —
strings and floats need a data section and ABI decisions, pointers need the
store (Stage C), closures need ADR-012's runtime.

Consequence: `Instr.const dst v` is only encodable when `v` is `.int` (in
range), `.bool`, or `.unit`. That is a *syntactic* check on the MIR function,
which means the encoder can reject rather than miscompile — consistent with
D-4's "strict, explicitly-listed subset" and with rejection being golden-tested.

## 2. Architecture correction: there are two IRs called MIR

ADR-032 §2 fact 1 says the MIR→CLIF function "is a Lean function; its Rust
transcription emits CLIF by in-process function calls", and its Consequences
say "`compiler` emits CLIF from MIR". Grounded state of the Rust workspace:

- `compiler/src/codegen/morph_ir.rs` defines `MorphIRModule` with
  `Instruction::{PushInt, PushFloat, PushBool, PushStr, PushUnit, PushNull,
  LoadLocal, StoreLocal, LoadUpvalue, StoreUpvalue, Add, Sub, Mul, Div, Mod,
  Neg, Not, Eq, Ne, Lt, Gt, …}` — a **stack machine with locals and
  upvalues**.
- Lean's `Morph.MIR` (`Morph/MIR.lean:107`) is **SSA, register-keyed**, with
  `ValId` destinations, `Block`s and `Terminator`s.

These are not the same IR, and the Rust one is not a transcription of the Lean
one: `LoadLocal`/`StoreUpvalue`/`PushStr` have no Lean MIR counterpart, and
Lean MIR's `phi`/block structure has no Rust counterpart. So the premise behind
"the Rust transcription of the Lean function" does not hold today — a Rust
implementation of MIR→CLIF would be a second, independent lowering from a
different input language, doubling the unverified surface ADR-032 set out to
minimise.

**Correction, in the spirit of ADR-032 rather than against it.** ADR-032's
stated goal is "no marshalling layer at the verified/trusted boundary". The way
to actually get that is to run the *proved* function, not to re-implement it:

```
Lean executable                 Rust (trusted)
surface .morph
  → HIR        (proved)
  → MIR        (proved)
  → CLIF text  (proved printer, §4.3)
      ──────────────────────────→ cranelift-reader parses the text
                                  → cranelift-codegen lowers to machine code
                                  → object file → linker
```

- `Main.lean` already defines a `lean_exe morph` with a command table
  (`eval`/`parse`/`check`/`run`/`run --hir`/`fmt`/`doc`/`version`), so the Lean
  side of this is an additional command, not a new binary.
- The Rust side shrinks to: drive Cranelift, write the object file, invoke the
  linker, and differential-test. `compiler/src/codegen` (the AST→MorphIR
  stack lowering) is then **not on the Stage B path at all**.

This changes a recorded ADR-032 consequence (who emits CLIF), not its decision
(Cranelift, verified lowering). ADR-032 carries a dated amendment note pointing
here. The audit questions it raises — does the text boundary count as
marshalling, and is it acceptable as the proved/trusted seam — are recorded in
§8.

## 3. The Stage B subset (D-4 contract for codegen)

**Input gate:** `lowerProgram prog = some func` and `StraightStmts 256
prog.stmts` (Stage A's fragment), **plus** the encoder-side checks below, which
are syntactic and therefore rejectable.

| MIR construct | Stage B | Reason |
| --- | --- | --- |
| `const dst (.int n)` | IN, `n` in i64 range | `iconst.i64` |
| `const dst (.bool b)` | IN | `iconst.i8` 0/1 |
| `const dst .unit` | IN (no instruction) | destination never read |
| `const dst` other payloads | **reject** | §1.4 |
| `copy dst src` | IN (elided) | SSA rename, no CLIF value created |
| `unop dst .not src` | IN | `bnot.i8` over booleans |
| `unop dst .notb src` | IN | `bnot.i64` |
| `binop dst .add/.sub/.mul` | IN, range-hypothesised | §1.1 |
| `binop dst` comparisons (`eq neq lt leq gt geq`) | IN | `icmp` → i8, widened on use |
| `binop dst` bool `and`/`or` | IN | `band`/`bor` on i8 |
| `binop dst .andb/.orb/.xorb` | IN | i64 bitwise |
| `binop dst .shl/.shr` | IN, amount `< 64` | §1.3 |
| `binop dst .div/.mod` | **reject** | §1.2 |
| `binop dst .not` | **reject** | `BinOp.not` is a unary op encoded as `UnOp.not`; a `binop` carrying it is malformed and lowering must not produce it — the encoder asserts rather than guesses |
| `load`/`store`/`alloc`/`free` | **reject** | needs the store; Stage C with ABI lemmas |
| `call` | **reject** | `evalInstrFull`'s `.call` is `none`; no MIR semantics to be correct against |
| `phi` | **reject** | single block |
| `allocClosure`/`callClosure` | **reject** | ADR-012 runtime, Stage C/D |
| `Terminator.return_ src` | IN | `return` |
| any block other than the entry block | **reject** | single block |

Every reject is a `none` (or a typed `CodegenError`) with a golden test, like
`lowerExpr`'s `none` cases and the `--hir` path's exit-1 message.

**Where the shipped encoder is narrower than this table (loops 146, 148).** The
table is the *contract*; `Morph/ClifLower.lean` is what exists, and it rejects
four rows the table marks IN. Each rejection is deliberate, and each has an
agreement lemma that would otherwise have to paper over a real semantic
difference:

| Row above | What the encoder does | Why |
| --- | --- | --- |
| `.andb`/`.orb`/`.xorb` | rejects | the MIR oracle defines them by **parity**, so they agree with `band`/`bor` only on `{0,1}`; `xorb` has no CLIF spelling in the subset at all |
| `.not` (unop) | rejects | `.not` is boolean negation on a `bool` value; `bnot` is the i64 complement, a different function. `.notb` is the row that pairs with `bnot` |
| `copy` | rejects | CLIF has no copy: an elision needs the two registers to be *identified* afterwards, which is a renaming pass, not an instruction |
| `const` with a `bool` payload | rejects | `iconst.i8` is a different value domain from `Value.bool`; the agreement lemma would claim `band`-on-i8 equals `and`-on-bool, which is true only for the free theorem, not for the model as built |

So Stage B's actual input gate is narrower than the table and B6's golden tests
must be written against the encoder, not against the table. The table is kept as
the contract to grow into; the four gaps are what a Stage C (bool/i8 domain) or a
renaming pass would close.

## 4. Target theorem statements (design, not implemented)

Names are proposals; nothing below exists in the tree yet.

### 4.1 The CLIF model

A Lean inductive for the CLIF subset actually emitted — `iconst`, `iadd`,
`isub`, `imul`, `icmp`, `band`, `bor`, `bnot`, `ishl`, `sshr`, `return` — plus a
block/function wrapper, a value map from CLIF value numbers to `Value`, and an
evaluator `runClif : ClifFunc → Option Value` that runs the entry block and
returns its `return` operand. Deliberately *not* a model of CLIF in general: it
covers the instructions the encoder can emit and nothing else, so every
instruction in the model has a proved agreement lemma (an unused instruction
would be an unproved obligation, which is the failure mode to avoid).

Fixed-width arithmetic is modelled with an explicit `wrap : Int → Int` so the
range hypothesis has something to discharge. `wrap` is the identity on
representable values (`wrap_eq_self`), and each arithmetic op is
`wrap (a ⊕ b)`.

### 4.2 The simulation lemma (primary form)

```
clif_simulate :
  ∀ (is : List Instr) (fenv fenv' : FullEnv) (cenv cenv' : ClifEnv),
    execInstrsFull fenv is = some fenv' →
    Agree fenv cenv →
    ∃ cenv'', execClif cenv (translate is) = some cenv'' ∧ Agree fenv' cenv''
```

`Agree fenv cenv` is the whole hypothesis: the register map takes each bound
`ValId` to the CLIF value holding the same `Value`, **and** every `Int` bound in
`fenv` lies in i64 range. `translate` is order-preserving and elides `copy`, so
the map only grows.

Stated by simulation over the instruction list rather than as "run MIR, then run
the whole listing", because §1.1's range condition has to be *inductive*: it is
carried in `Agree` and re-established at each step, which a whole-program
statement cannot express without a trace predicate over `execFunc`'s opaque
result.

Each `Instr` constructor contributes one case, each discharged by a per-operator
lemma of the shape `executable.evalBinop .add (.int a) (.int b) = some (.int
(a+b))` on one side and `clifIAdd a b = wrap (a+b)` on the other, with
`wrap_eq_self` needing exactly the range fact `Agree` carries.

`Agree` must also be *initialised*, which is where the encoder's own checks do
their work: at function entry the register map holds the parameters (empty for
the Stage B subset, since a straight-line fragment has no parameters yet) and
the function's `const` payloads are already restricted to §1.4's encodable set,
so no `Agree` case is left unreachable.

### 4.3 The composer and the printer

```
clif_correct :
  StraightStmts 256 ss → encodable func →
  execFunc 2 func ⟨fun _ => none, store⟩ = some w →
  Representable w →
  runClif (emitClif func) = some w
```

and, for the text boundary of §2:

```
render_parse_id : parseClif (renderClif f) = some f
```

`parseClif` is a Lean parser for exactly the renderer's output grammar. This does
not prove Cranelift parses it (impossible from inside Lean); it proves the
renderer is injective on the model's instructions, so a parse failure on the Rust
side is a *grammar* bug, not a lost value. That is the strongest statement
available at this boundary and it should be described as exactly that, not as
verified marshalling.

## 5. Work items and exit criteria (ordered)

| # | Item | Exit criterion |
| --- | --- | --- |
| B1 | CLIF model + `wrap` lemmas + `runClif` | `lake env lean` clean, no `sorry`, `wrap_eq_self` proved |
| B2 | `translate`/`emitClif` for the §3 IN set, rejects elsewhere | every §3 reject has a `none`/error case |
| B3 | per-operator agreement lemmas | each IN operator has one, `rfl`-adjacent where possible |
| B4 | `clif_simulate` + `clif_correct` (met, loop 148) | composes with `compile_total`; no failure-coincidence claim |
| B5 | `renderClif`/`parseClif` + `render_parse_id` (met at token level, loop 149) | round-trip proved; grammar documented |
| B6 | `morph build --codegen=cranelift` in `Main.lean` behind the flag (met, loop 150) | in-subset file → exit 0 + `.clif` artifact; out-of-subset → exit 1 with the D-4 message; both golden-tested |
| B7 | Rust `codegen` driver: `cranelift-reader` → `cranelift-codegen` → object → link | builds and runs the B6 golden corpus |
| B8 | differential bridge: native result vs `morph run` result over the corpus | corpus green; corpus contents listed in the packet |
| B9 | audit-packet refresh: Cranelift version pinned, TCB section updated | packet names the new trusted components |

**Status (loop 148):** B1 is `Morph/ClifTarget.lean`, B2/B3 are
`Morph/ClifLower.lean`, B4 is `Morph/ClifSimulate.lean` +
`Morph/ClifCorrect.lean`; all green with no `sorry` and no warnings. B4 is
**met**: `clif_correct` turns an encoded block plus a `Trace` into a statement
about `Clif.run`, and `clif_correct_program` composes it with `compile_total`
into one conjunction over the same HIR value — `execFunc 2 (lowerProgram prog) =
some (.int n) ∧ Clif.run cf = some (.int n)`. Two caveats are recorded in the
files rather than hidden: the range/typing hypothesis is a *premise* of B4,
carried by `Step` (nothing proves that a source program stays in range), and
`lowerProgram`'s `.const 0 .unit` prologue is *dropped* from the emitted
function, with `Trace` starting at `update (fun _ => none) 0 .unit` and
transported to the empty register file by `AgreesOnValues`.
Two model details settled while doing B3 and worth recording: `bnot` is the i64
complement (`-a - 1`) and therefore pairs with `.notb`, not with `.not`, which
is boolean negation; `sshr` computes `Int.shiftRight`, the oracle's own
primitive, so the shift agreement is definitional. `.shl` spells its power as
`Int.pow 2 n` — the oracle's spelling — because `Int.pow 2 n` and `(2 : Int)^n`
are not interchangeable under `rfl` in every position, and a syntactic match is
cheaper than a bridge lemma.

**B5 (loop 149)** is `Morph/ClifRender.lean`. The round trip is proved at the
*token* level — `parseFunc_toksFunc : parseFunc (toksFunc f) = some f`, with the
stream framed by a `function` marker, an instruction count, and the returned
register — and `parseFunc_toksFunc_append` closes the other direction: nothing
may follow the return, so the printer's image is exactly the parser's domain.
The token units are self-delimiting (each carries its payload and its name fixes
its arity), which is why the parser is total, structural in its fuel, and
invertible without backtracking; the grammar is written out at the top of the
file.

The *text* half is deliberately not a round trip. `renderFunc` emits the CLIF
the artifact ships, and its reader is `cranelift-reader`, already trusted per
ADR-032 §3; a Lean re-implementation of the CLIF lexer would put more code in
the TCB, not less. What is proved is that the units we emit are the units we
mean, and the grammar is stated so the text can be read against a specification
rather than an assumption. If a later stage wants the byte-level round trip for
its own sake, the missing piece is a tokenizer, and it would be new untrusted
surface rather than new assurance about the compiler.

**B6 (loop 150)** is `Morph/ClifEmit.lean` plus a `buildClif` in
`Morph/Driver.lean` and one arm in `Main.lean`. The interesting decision is the
one about the prologue: `lowerProgram` always emits `.const 0 .unit` first so
that register 0 holds unit, and CLIF has no unit value. Rather than invent an
encoding for it, `emitBlock` *requires* that instruction and drops it, so the
artifact is `blockEncode` of the body alone — `emitBlock_prologue` and
`emitClif_lowered` are `rfl`, i.e. the emitter is definitionally the verified
encoder on the shape `lowerProgram` produces, with no prologue instruction in
the text. Dropping it is sound because register 0 is that instruction's own
destination: B4's trace starts at an environment where 0 already holds unit.

**A defect found by writing the corpus, fixed (loop 151).** A program whose value
is unit (`let y = 5;`, or the empty program) lowers to `return_ 0` — the
prologue's own register — and the first emitter printed `return %v0`, naming a
value no instruction defines. B4's *model* is fine with that (its trace starts at
an environment where 0 already holds unit), but the text is not CLIF, and
`cranelift-reader` would reject it. `emitBlock` now refuses `retSrc = 0`
(`emitBlock_unit`), so the model/emitter gap is visible and rejectable rather
than deferred to the reader. This is the third place the text is narrower than
the model, alongside the prologue and §3's reject list.

Three rejections are distinct, because they mean different things to a user:
outside the HIR fragment (stage A's gate), outside the stage-B MIR fragment
(`lowerProgram` returned `none`), and inside MIR but unencodable (`blockEncode`
returned `none` — exactly §3's reject list). Each has a golden test, and so does
the accept path, byte for byte, in `Morph/Tests/Driver.lean`. What the tests pin
is the `Outcome`, which is also the exit code: `Main.lean` writes the `.value`
text to `clifArtifactPath path` (`main.hum` → `main.clif`, only the last path
component's extension touched) and returns 0; every other outcome prints to
stderr and returns 1, with no artifact left behind.

B1–B6 are pure Lean and are the Stage B exit. B5 is what makes B6's artifact
meaningful, and B6 is where the proof stops being only a proof. B7–B8 are the
unverified half and are gated as trusted code, with the differential corpus as
their only evidence — which is what ADR-032 §3 already says, now with a work
breakdown under it.

B1–B6 carry no `sorry` at any point; each lands green or not at all. This is the
same discipline Stage A used, and it is why Stage A did not need a
"sorry-temporarily" exception.

## 6. Differential bridge, concretely

- **Oracle A (proved-relative):** `Morph.MIR.execFunc` — what
  `compile_total` concludes about.
- **Oracle B (trusted):** the native binary built from the emitted CLIF, run
  with the same `store`-free initial environment.
- **Corpus:** one program per §3 IN row, one per arithmetic edge case in range
  (negative operands for comparisons, shift amounts 0/1/63, i64 min/max
  constants), and the reject cases as negative tests. Written as `.morph`
  sources under the existing test tree so `morph run` and `morph build` consume
  the same input.
- **What disagreement means:** a divergence is either a translation bug, a
  Cranelift lowering bug, or a gap in `Agree`'s range hypothesis — *not* a
  lowering-proof bug, and the triage order is recorded here so the first
  divergence is diagnosed rather than guessed at.

## 7. What Stage B will not claim

- Not that emitted machine code is correct. The proved chain ends at CLIF.
- Not that Cranelift is correct, nor that the parse of the rendered text is
  faithful (only that the renderer is injective).
- Not unconditional value preservation: §1.1's range hypothesis is a real
  hypothesis. A program that overflows in MIR gets no Stage B claim, and the
  D-4 document says so in user-facing terms.
- Not `div`/`mod` (§1.2) or any memory, call, or closure construct.
- Not "CLIF trapped ⇒ MIR stalled" — the one-directional discipline is
  inherited unchanged from `agreeBoth`/`compile_total`.

## 8. Open decisions for the audit (not decided here)

1. **Is a rendered-text boundary acceptable as the proved/trusted seam?** §2
   moves the seam from "Rust transcription of a Lean function" to "Lean
   renders CLIF, Cranelift parses it". The first is a re-implementation
   (larger trusted surface, no proof); the second is a format boundary with an
   injectivity proof (smaller surface, and a parse failure is loud). The note
   recommends the second, per ADR-032's own criterion, but the audit question
   ADR-032 recorded was about lowering-vs-TD, not about where the seam sits.
2. **Does the range hypothesis belong in the user-facing contract, or should
   the compiler emit checked wraparound?** Checked arithmetic would make
   overflow a trap and the theorem unconditional, at a cost in code
   quality and a semantic divergence in the other direction (MIR defines the
   wrapped value). Default on silence: hypothesis in the contract, unchecked
   arithmetic, documented under D-4.
3. **Should `div`/`mod` ship in B1 behind the strict-subset gate as rejects, or
   wait for the guarded sequence?** Default: reject in B1 (a `none` is honest;
   an `sdiv` is a miscompile), guarded sequence as B-series follow-on.
