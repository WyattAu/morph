/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LayeredConcurrency.Spec

namespace Morph.Specs.LayeredConcurrency.Examples

/- # Examples for Layered Concurrency Architecture -/

/-- Simple counter application demonstrating unidirectional state management -/
structure CounterState where
  count : Nat
  deriving Repr, BEq

/-- Counter events for increment and decrement -/
inductive CounterEvent where
  | increment : CounterEvent
  | decrement : CounterEvent
  | getValue : CounterEvent
  deriving Repr, BEq

/-- Counter reducer: pure function producing new state from event -/
def counterReducer : Reducer := fun state event =>
  match event with
  | .increment => { count := state.count + 1 }
  | .decrement => { count := state.count - 1 }
  | .getValue => state

/-- Counter command: descriptor for state transitions -/
def counterCommand : Command := fun _ event =>
  match event with
  | .increment => fun state => { count := state.count + 1 }
  | .decrement => fun state => { count := state.count - 1 }
  | .getValue => fun state => state

/-- Example application layer state with counter -/
def exampleApplicationLayer : ApplicationLayerState :=
  { state := { count := 0 }
    reducer := counterReducer
    command := counterCommand }

/-- Example counter actor with mailbox and behavior -/
def exampleCounterActor : Actor :=
  { mailbox := { messages := [] }
    state := { count := 0 }
    behavior := {
      process := fun msg _ =>
        match msg.content with
        | .str "increment" =>
          ({ count := defaultState.count + 1 }, some { content := .str "incremented", sender := msg.sender })
        | .str "decrement" =>
          ({ count := defaultState.count - 1 }, some { content := .str "decremented", sender := msg.sender })
        | .str "get" =>
          ({ count := defaultState.count }, some { content := .str (s!"{defaultState.count}"), sender := msg.sender })
        | _ =>
          (defaultState, none)
      }
    }

/-- Example layer boundary for spawning, sending, and receiving -/
def exampleLayerBoundary : LayerBoundary :=
  { spawn := fun id app =>
      { mailbox := { messages := [] }
        state := app.state
        behavior := {
          process := fun msg _ =>
            ({ app.state }, some msg)
          }
      }
    send := fun id msg app =>
      { app with state := app.reducer app.state (.str "send") }
    receive := fun id msg app =>
      { app with state := app.reducer app.state (.str "receive") }
  }

/-- Verify unidirectional state flow: all transitions are forward -/
example verifyUnidirectionalFlow : stateTransitionsFlowUnidirectional exampleApplicationLayer.state := by
  intro s1 s2 e
  exists { from := s1, event := e, to := s2, direction := .forward }
  constructor <; rfl <; rfl <; rfl <; rfl

/-- Verify pure function properties: no side effects, deterministic -/
example verifyPureFunction : isPureFunction counterReducer := by
  constructor
  · intro s1 s2 e1 e2 h_eq
    cases h_eq
    rfl
  · intro s e
    cases e
    < rfl
    < rfl
    < rfl
  · intro s1 s2 e h_det
    exact h_det

/-- Verify bidirectional messaging: actor can send and receive -/
example verifyBidirectionalMessaging : supportsBidirectionalMessaging exampleCounterActor.behavior := by
  exists { content := .str "test", sender := { id := 0 } }
  exists { content := .str "response", sender := { id := 0 } }
  intro msg response
  unfold supportsBidirectionalMessaging
  unfold Behavior.process
  unfold defaultState
  unfold Message.content
  unfold ActorId.id
  constructor <; rfl <; rfl <; rfl

/-- Verify layer boundary is well-defined: all operations produce valid results -/
example verifyLayerBoundary : wellDefinedLayerBoundary exampleLayerBoundary := by
  constructor
  · intro id app
    unfold wellDefinedSpawnBoundary
    unfold LayerBoundary.spawn
    unfold exampleLayerBoundary
    unfold Actor.ne
    unfold defaultState
    intro h_eq
    contradiction
  · intro id msg app
    unfold wellDefinedSendBoundary
    unfold LayerBoundary.send
    unfold exampleLayerBoundary
    unfold ApplicationLayerState.ne
    unfold defaultState
    intro h_eq
    contradiction
  · intro id msg app
    unfold wellDefinedReceiveBoundary
    unfold LayerBoundary.receive
    unfold exampleLayerBoundary
    unfold ApplicationLayerState.ne
    unfold defaultState
    intro h_eq
    contradiction

/-- Verify no shared state: application and actor states are separate -/
example verifyNoSharedState : noSharedStateBetweenLayers exampleApplicationLayer exampleCounterActor := by
  intro sApp sActor h_app_eq h_actor_eq
  cases h_app_eq
  rfl
  cases h_actor_eq
  rfl

end Morph.Specs.LayeredConcurrency.Examples
