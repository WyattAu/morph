/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Runtime

/-!
# Actor progress: the D3 statement, made real (S16 pulled forward)

`docs/STAGED-SCOPE.md` §4 sketches `actors_progress` — a well-formed actor
system never gets stuck without a witness. The sketch's names were
placeholders; this module makes them real against the Reading-A `stepActor`
(ADR-033; the interface decision is recorded, so drafting was unblocked
ahead of the S16 slot by maintainer direction).

What is here:

* `WFActors` — distinct actor ids (routing and the round-robin index name
  actors by id, so duplicates would make `send`/`recv` ambiguous).
* `DeadlockWitness` — the stuck step's witness: the scheduled actor, its
  pool position, the scheduling equation, and its failing evaluation.
* `actors_progress` — **proved**: a stuck step always carries such a
  witness. Note the statement is stronger than the sketch: no `WFActors`
  hypothesis is needed — a stuck step is witnessed whether or not the
  system is well-formed.

What is deliberately not here (the §7 maintainer calls): the global
invariant D3 preserves (mailbox boundedness vs crash containment), and the
`stepActor` preservation obligations that invariant will bring. `WFActors`
preservation is the first candidate pin once that choice lands.
-/

namespace Morph.ActorProgress

open Morph.Runtime Morph.Executable Morph.Syntax Morph.Core

/-! ## Well-formedness -/

/-- Distinct actor ids: routing (`send`/`recv` match on `Actor.id`) and the
round-robin index both name actors by id, so duplicates would make the
scheduler and the mailbox ambiguous. -/
def WFActors (system : ActorSystem) : Prop :=
  (system.actors.map Actor.id).Nodup

/-! ## The witness -/

/-- A stuck step is witnessed by the scheduled actor: it exists in the pool
at the round-robin position, and its state expression failed to evaluate
within the fuel budget. -/
structure DeadlockWitness (system : ActorSystem) (fuel turn : Nat) where
  actor : Actor
  atIdx : Nat
  scheduled : system.actors[atIdx]? = some actor
  scheduledIdx : atIdx = turn % system.actors.length
  unevaluable : evalWithFuel fuel Context.empty actor.state = none

/-! ## Progress -/

/-- **A stuck step is witnessed** (D3 statement, S16 exit shape). Stronger
than the §4 sketch: no `WFActors` hypothesis is needed — a stuck step names
the scheduled actor and its failing evaluation whether or not the system is
well-formed. -/
theorem actors_progress (system : ActorSystem) (fuel turn : Nat)
    (heap : Heap) (stack : Stack) :
    stepActor fuel system turn heap stack = (.stuck, system, heap, stack) →
    Nonempty (DeadlockWitness system fuel turn) := by
  unfold stepActor
  cases hidx : system.actors[turn % system.actors.length]? with
  | none => intro heq; simp at heq
  | some actor =>
      cases hval : evalWithFuel fuel Context.empty actor.state with
      | none =>
          intro heq
          exact ⟨⟨actor, turn % system.actors.length, hidx, rfl, hval⟩⟩
      | some v => intro heq; simp [stepActor, hval] at heq

/-- **Stuck steps contain themselves**: when a step is stuck, the returned
system is the input system — the failed evaluation left every other actor's
state, every mailbox, and `nextId` untouched. This is the D3 containment
fact under Reading A, and it is definitional: the stuck branch returns the
input system verbatim. -/
theorem stepActor_stuck_system_unchanged (system : ActorSystem) (fuel turn : Nat)
    (heap : Heap) (stack : Stack)
    (h : (stepActor fuel system turn heap stack).1 = .stuck) :
    (stepActor fuel system turn heap stack).2.1 = system := by
  unfold stepActor
  cases hidx : system.actors[turn % system.actors.length]? with
  | none => rfl
  | some actor =>
      cases hval : evalWithFuel fuel Context.empty actor.state with
      | none => simp [stepActor, hval] at h ⊢
      | some v => simp [stepActor, hidx, hval] at h

/-! ## Pins -/

/-- The empty pool steps trivially. -/
example : stepActor 256 emptyActorSystem 0 [] [] =
    (.stepped, emptyActorSystem, [], []) := rfl

/-- A literal-state actor steps and keeps its value: completion is
idempotent. -/
private def aLit : Actor := { id := 0, state := .lit (.int 3), mailbox := [] }

private def sysLit : ActorSystem := { actors := [aLit], nextId := 1 }

example : (stepActor 256 sysLit 0 [] []).1 = .stepped := rfl

example : (stepActor 256 sysLit 0 [] []).2.1.actors[0]? =
    some { id := 0, state := .lit (.int 3), mailbox := [] } := rfl

/-- An unbound variable sticks — with a witness naming the actor. -/
private def aFvar : Actor := { id := 0, state := .fvar "x", mailbox := [] }

private def sysFvar : ActorSystem := { actors := [aFvar], nextId := 1 }

example : (stepActor 256 sysFvar 0 [] []).1 = .stuck := rfl

example : Nonempty (DeadlockWitness sysFvar 256 0) :=
  ⟨⟨aFvar, 0, rfl, rfl, rfl⟩⟩

/-- Fuel exhaustion is `stuck`, witnessed the same way. -/
example : Nonempty (DeadlockWitness sysFvar 0 0) :=
  ⟨⟨aFvar, 0, rfl, rfl, rfl⟩⟩

end Morph.ActorProgress
