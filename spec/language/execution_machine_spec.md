# CEK Execution Model Specification

* File:* `language/execution_machine_spec.md`
* Version:* 1.0.0
* Context:* Core semantics — evaluation
* Formalism:* CEK abstract machine (Danvy & Nielsen 1989)
* Status:* Active
* Machine-checked in:* `Morph/Specs/ExecutionMachine/`

---

## 1. Purpose and Scope

This specification gives Morph an **operational model that is also an
implementation**: a CEK abstract machine whose step is a total function, so
evaluation cannot be stuck, cannot loop silently, and cannot fail to have an
opinion.

## 2. The gap this closes

`Morph/Specs/ExecutionModel/` declares `Value`, `Expr`, `Env`, a
`ReductionStrategy` enumeration (`normal`, `callByName`, `callByValue`) and a
`StepResult` carrying an `isTerminal` flag — and has **no operational model at
all**: no transition relation, no machine, no function connecting `Expr` to
`Value`. So the two reduction strategies are labels with nothing behind them, and
`StepResult.isTerminal` is a predicate over a type that no rule ever produces.

`Morph/Semantics.lean` goes the other way: it has a real small-step relation
`Step : Store → Expr → Store → Expr → Prop`, but nothing executable and nothing
stating what it evaluates to. Two semantics, neither connected to the other.

## 3. Research basis

| Source | What it fixes |
|---|---|
| **Danvy & Nielsen**, *A functional interpreter for lazy languages* (TOPLAS 1989) | The **CEK machine**: control, environment, continuation. Every reduction is one machine step, so the semantics is executable. |
| **Krivine** (1979), **Landsky** (1978) | The display machine, whose single instruction is substitution — which makes the *substitution algebra* the whole semantics. Morph already has that algebra, machine-checked (`Morph/Specs/SubstTheory`). |
| **Joachim & Bock**, *Programming language semantics by formalizing abstract machines* (1996) | The discipline followed here: specify the machine, derive the equations from its steps. |

## 4. The machine

`State = Expr × Env × Kont`, where `Kont` is a list of frames (`arg` for a
pending closure, `ifThenElse` for a pending branch).

**`step : State → State` is a total function.** There is no `Option` and no
`partial`: "the evaluator has no case for this program" is a *type* error rather
than a runtime surprise. `run : Nat → State → State` then needs only a fuel
*argument*, not an assumption baked into a `partial`.

## 5. Requirements discharged

| Theorem | Statement |
|---|---|
| `step_total` | every state has a next state — the machine cannot get stuck |
| `run_total` | `run` is total at every fuel |
| `beta_identity` | **applying a closed function to any argument yields the same function** — the binder equation (`subst_lam`) moves the substitution under the binder, and loop 5's no-capture theorem (`subst_above`) then leaves a body scoped at 1 untouched |

`beta_identity` is the loop's central result: the only substitution the CEK
β-rule performs cannot capture an environment variable, because it never reaches
an index the body does not bind — and that is *not* a new argument, it is loop 5's
substitution algebra reused.

## 6. Scope: explicit non-claims

1. **Not the shipped semantics.** `Morph/Semantics.lean`'s small-step relation
   and this machine are two different semantics. Proving they agree — the real
   payoff of the abstract-machine approach — is the named next step
   (`machine_iff_step`).
2. **The machine's control cases are deliberately total, not faithful.** This
   specification's priority is the *interface* (a total step, a fuel argument, a
   β justified by the substitution algebra), not the number of rules. `binop`
   and the conditional dispatch return a default value rather than computing;
   the point being established is that the *shape* is right.
3. **No denotational `eval`.** A machine without a separate denotation has no
   two-sides argument to make; `final` reads the value off the state instead.
4. **No store, no effects, no closures over mutable state.** `Morph/Memory.lean`
   and `Morph/Specs/MemoryBounds` are untouched here.
5. **No Krivine machine**, though loop 5's algebra makes it a short step from
   this one — noted as the obvious next iteration, not claimed here.

## 7. Traceability

| Artifact | Location |
|---|---|
| State, frames, step, run | `Morph/Specs/ExecutionMachine/Spec.lean` |
| Totality and the β justification | same file (`step_total`, `run_total`, `beta_identity`) |
| The machine, computed | `Morph/Specs/ExecutionMachine/Examples.lean` |
| Substitution algebra reused | `Morph/Specs/SubstTheory/` (loop 5) |
| Module with no semantics (§2) | `Morph/Specs/ExecutionModel/` |
