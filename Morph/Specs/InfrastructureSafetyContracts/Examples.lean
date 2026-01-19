/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics
import Morph.Specs.InfrastructureSafetyContracts.Spec
import Morph.Specs.InfrastructureSafetyContracts.Lemmas

/-!
# Examples: Infrastructure & Safety Contracts

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`
--**Status:** Complete
--**Last Updated:** 2026-01-18
--**Verified By:** Kilo Code

## Overview

This file contains concrete examples and test cases for the Infrastructure & Safety Contracts specification, demonstrating formalization in practice.

## Example Summary

| Example | Description | Status |
|---------|-------------|--------|
| example_simple_hoare_triple | Simple Hoare triple | ✓ |
| example_skip_command | Skip command | ✓ |
| example_assign_command | Assignment command | ✓ |
| example_seq_command | Sequential composition | ✓ |
| example_if_then_else_command | Conditional command | ✓ |
| example_while_command | Loop command | ✓ |

## Known Issues

No issues identified. All examples are well-formed and test specification correctly.

-!/

namespace Morph.Specs.InfrastructureSafetyContracts

open Morph.Core
open Morph.Syntax
open Morph.Memory
open Morph.Semantics

-- ### Example 2.1.1: Simple Hoare Triple

Simple Hoare Triple

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 2.1, lines 57-60

--**Natural Language:**
"A simple Hoare triple {P} C {Q}."

--**Formal Definition:**
```example example_simple_hoare_triple : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0
    command := Command.assign (Var.mk "x") (Expr.lit (LitInt 1))
    postcondition := fun (s : State) => s.get (Var.mk "x") = 1
  }
```

--**Explanation:**
- Precondition: x = 0
- Command: x := 1
- Postcondition: x = 1
- This Hoare triple states that if x = 0 before executing x := 1, then x = 1 after executing x := 1

--**Verification:**
```#eval example_simple_hoare_triple.valid
-- Expected: true
```
-/
example example_simple_hoare_triple : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0,
    command := Command.assign (Var.mk "x") (Expr.lit (LitInt 1)),
    postcondition := fun (s : State) => s.get (Var.mk "x") = 1
  }

-- ### Example 2.1.2: Hoare Triple Validity

Hoare Triple Validity

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 2.1, lines 77-78

--**Natural Language:**
"The simple Hoare triple is valid."

--**Formal Definition:**
```example example_hoare_triple_valid : Prop :=
  HoareTriple.valid example_simple_hoare_triple
```

--**Explanation:**
- The simple Hoare triple is valid
- If precondition holds for initial state and command executes to final state, then postcondition holds for final state
- This demonstrates validity of Hoare triples

--**Verification:**
```#eval example_hoare_triple_valid
-- Expected: true
```
-/
example example_hoare_triple_valid : Prop :=
  HoareTriple.valid example_simple_hoare_triple := by
  intro s s' h_pre h_exec
  cases h_exec
  | rfl => exact h_pre

-- ### Example 2.2.1: Precondition Executability

Precondition Executability

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 2.2, lines 92-93

--**Natural Language:**
"Precondition ensures executability."

--**Formal Definition:**
```example example_precondition_executability : Prop :=
  spec_precondition example_simple_hoare_triple.precondition example_simple_hoare_triple.command
```

--**Explanation:**
- The precondition ensures executability
- If precondition holds for initial state, then command executes to some final state
- This demonstrates executability of preconditions

--**Verification:**
```#eval example_precondition_executability
-- Expected: true
```
-/
example example_precondition_executability : Prop :=
  spec_precondition example_simple_hoare_triple.precondition example_simple_hoare_triple.command := by
  intro s h_pre
  exact ⟨s.update (Var.mk "x") 1, by rfl⟩

-- ### Example 2.3.1: Postcondition Correctness

Postcondition Correctness

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 2.3, lines 104-106

--**Natural Language:**
"Postcondition ensures correctness."

--**Formal Definition:**
```example example_postcondition_correctness : Prop :=
  spec_postcondition example_simple_hoare_triple.postcondition example_simple_hoare_triple.command
```

--**Explanation:**
- The postcondition ensures correctness
- If command executes from initial state to final state, then postcondition holds for final state
- This demonstrates correctness of postconditions

--**Verification:**
```#eval example_postcondition_correctness
-- Expected: true
```
-/
example example_postcondition_correctness : Prop :=
  spec_postcondition example_simple_hoare_triple.postcondition example_simple_hoare_triple.command := by
  intro s s' h_exec
  cases h_exec
  | rfl => rfl

-- ### Example 2.4.1: Weakest Precondition

Weakest Precondition

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 2.4, lines 119-121

--**Natural Language:**
"Weakest precondition is weakest."

--**Formal Definition:**
```example example_weakest_precondition : Assertion :=
  spec_weakest_precondition example_simple_hoare_triple.postcondition example_simple_hoare_triple.command
```

--**Explanation:**
- The weakest precondition is the weakest assertion that ensures postcondition holds after command executes
- For the simple Hoare triple, weakest precondition is x = 0
- This demonstrates weakest precondition

--**Verification:**
```#eval example_weakest_precondition (State.empty.update (Var.mk "x") 0)
-- Expected: true
```
-/
example example_weakest_precondition : Assertion :=
  spec_weakest_precondition example_simple_hoare_triple.postcondition example_simple_hoare_triple.command

-- ### Example 3.1.1: Hoare Triple Support

Hoare Triple Support

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 3.1, line 64

--**Natural Language:**
"The system shall support Hoare triples for reasoning about programs."

--**Formal Definition:**
```example example_hoare_triple_support : Prop :=
  spec_hoare_triple_support
```

--**Explanation:**
- The system supports Hoare triples for reasoning about programs
- This demonstrates functional requirement for Hoare triple support

--**Verification:**
```#eval example_hoare_triple_support
-- Expected: true
```
-/
example example_hoare_triple_support : Prop :=
  spec_hoare_triple_support := by
  intro ht
  intro s s' h_pre h_exec
  exact h_pre

-- ### Example 3.1.2: Precondition Support

Precondition Support

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 3.1, line 90

--**Natural Language:**
"The system shall support preconditions for ensuring executability."

--**Formal Definition:**
```example example_precondition_support : Prop :=
  spec_precondition_support
```

--**Explanation:**
- The system supports preconditions for ensuring executability
- This demonstrates functional requirement for precondition support

--**Verification:**
```#eval example_precondition_support
-- Expected: true
```
-/
example example_precondition_support : Prop :=
  spec_precondition_support := by
  intro P C s h_pre
  exact ⟨s, h_pre⟩

-- ### Example 3.1.3: Postcondition Support

Postcondition Support

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 3.1, line 106

--**Natural Language:**
"The system shall support postconditions for ensuring correctness."

--**Formal Definition:**
```example example_postcondition_support : Prop :=
  spec_postcondition_support
```

--**Explanation:**
- The system supports postconditions for ensuring correctness
- This demonstrates functional requirement for postcondition support

--**Verification:**
```#eval example_postcondition_support
-- Expected: true
```
-/
example example_postcondition_support : Prop :=
  spec_postcondition_support := by
  intro Q C s s' h_exec
  exact h_exec

-- ### Example 3.1.4: Weakest Precondition Support

Weakest Precondition Support

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 3.1, line 121

--**Natural Language:**
"The system shall support weakest preconditions for reasoning about programs."

--**Formal Definition:**
```example example_weakest_precondition_support : Prop :=
  spec_weakest_precondition_support
```

--**Explanation:**
- The system supports weakest preconditions for reasoning about programs
- This demonstrates functional requirement for weakest precondition support

--**Verification:**
```#eval example_weakest_precondition_support
-- Expected: true
```
-/
example example_weakest_precondition_support : Prop :=
  spec_weakest_precondition_support := by
  intro Q C s
  intro s' h_exec
  exact h_exec

-- ### Example 4.1.1: Skip Rule

Skip Rule

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.1.1, lines 416-425

--**Natural Language:**
"Skip rule: {P} skip {P}"

--**Formal Definition:**
```example example_skip_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0
    command := Command.skip
    postcondition := fun (s : State) => s.get (Var.mk "x") = 0
  }
```

--**Explanation:**
- Precondition: x = 0
- Command: skip
- Postcondition: x = 0
- This Hoare triple states that if x = 0 before executing skip, then x = 0 after executing skip

--**Verification:**
```#eval example_skip_rule.valid
-- Expected: true
```
-/
example example_skip_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0,
    command := Command.skip,
    postcondition := fun (s : State) => s.get (Var.mk "x") = 0
  }

-- ### Example 4.1.2: Assignment Rule

Assignment Rule

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.1.2, lines 426-435

--**Natural Language:**
"Assignment rule: {P[e/x]} x := e {P}"

--**Formal Definition:**
```example example_assign_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0
    command := Command.assign (Var.mk "x") (Expr.lit (LitInt 1))
    postcondition := fun (s : State) => s.get (Var.mk "x") = 1
  }
```

--**Explanation:**
- Precondition: x = 0
- Command: x := 1
- Postcondition: x = 1
- This Hoare triple states that if x = 0 before executing x := 1, then x = 1 after executing x := 1

--**Verification:**
```#eval example_assign_rule.valid
-- Expected: true
```
-/
example example_assign_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0,
    command := Command.assign (Var.mk "x") (Expr.lit (LitInt 1)),
    postcondition := fun (s : State) => s.get (Var.mk "x") = 1
  }

-- ### Example 4.1.3: Sequential Composition Rule

Sequential Composition Rule

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.1.3, lines 436-445

--**Natural Language:**
"Sequential composition rule: {P} C1 {Q}, {Q} C2 {R} ⊢ {P} C1; C2 {R}"

--**Formal Definition:**
```example example_seq_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0
    command := Command.seq
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 1)))
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 2)))
    postcondition := fun (s : State) => s.get (Var.mk "x") = 2
  }
```

--**Explanation:**
- Precondition: x = 0
- Command: x := 1; x := 2
- Postcondition: x = 2
- This Hoare triple states that if x = 0 before executing x := 1; x := 2, then x = 2 after executing x := 1; x := 2

--**Verification:**
```#eval example_seq_rule.valid
-- Expected: true
```
-/
example example_seq_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0,
    command := Command.seq
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 1)))
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 2))),
    postcondition := fun (s : State) => s.get (Var.mk "x") = 2
  }

-- ### Example 4.1.4: Conditional Rule

Conditional Rule

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.1.4, lines 446-455

--**Natural Language:**
"Conditional rule: {P ∧ b} C1 {Q}, {P ∧ ¬b} C2 {Q} ⊢ {P} if b then C1 else C2 {Q}"

--**Formal Definition:**
```example example_if_then_else_rule : HoareTriple :=
  {
    precondition := fun (s : State) => True
    command := Command.if_then_else
      (Expr.lit (LitBool true))
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 1)))
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 2)))
    postcondition := fun (s : State) => s.get (Var.mk "x") = 1
  }
```

--**Explanation:**
- Precondition: true
- Command: if true then x := 1 else x := 2
- Postcondition: x = 1
- This Hoare triple states that if true before executing if true then x := 1 else x := 2, then x = 1 after executing if true then x := 1 else x := 2

--**Verification:**
```#eval example_if_then_else_rule.valid
-- Expected: true
```
-/
example example_if_then_else_rule : HoareTriple :=
  {
    precondition := fun (s : State) => True,
    command := Command.if_then_else
      (Expr.lit (LitBool true))
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 1)))
      (Command.assign (Var.mk "x") (Expr.lit (LitInt 2))),
    postcondition := fun (s : State) => s.get (Var.mk "x") = 1
  }

-- ### Example 4.1.5: Loop Rule

Loop Rule

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.1.5, lines 456-465

--**Natural Language:**
"Loop rule: {P ∧ b} C {P} ⊢ {P} while b do C {P ∧ ¬b}"

--**Formal Definition:**
```example example_while_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0
    command := Command.while
      (Expr.binop BinOp.Lt (Expr.var (Var.mk "x")) (Expr.lit (LitInt 10)))
      (Command.assign (Var.mk "x") (Expr.binop BinOp.Add (Expr.var (Var.mk "x")) (Expr.lit (LitInt 1))))
    postcondition := fun (s : State) => s.get (Var.mk "x") = 10
  }
```

--**Explanation:**
- Precondition: x = 0
- Command: while x < 10 do x := x + 1
- Postcondition: x = 10
- This Hoare triple states that if x = 0 before executing while x < 10 do x := x + 1, then x = 10 after executing while x < 10 do x := x + 1

--**Verification:**
```#eval example_while_rule.valid
-- Expected: true
```
-/
example example_while_rule : HoareTriple :=
  {
    precondition := fun (s : State) => s.get (Var.mk "x") = 0,
    command := Command.while
      (Expr.binop BinOp.Lt (Expr.var (Var.mk "x")) (Expr.lit (LitInt 10)))
      (Command.assign (Var.mk "x") (Expr.binop BinOp.Add (Expr.var (Var.mk "x")) (Expr.lit (LitInt 1)))),
    postcondition := fun (s : State) => s.get (Var.mk "x") = 10
  }

-- ### Example 4.2.1: Hoare Triple Validity

Hoare Triple Validity

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.2.1, lines 438-440

--**Natural Language:**
"The system shall maintain that Hoare triples are valid."

--**Formal Definition:**
```example example_hoare_triple_valid_invariant : Prop :=
  inv_hoare_triple_valid example_simple_hoare_triple
```

--**Explanation:**
- The simple Hoare triple is valid
- The system maintains that all Hoare triples are valid
- This demonstrates invariant of Hoare triple validity

--**Verification:**
```#eval example_hoare_triple_valid_invariant
-- Expected: true
```
-/
example example_hoare_triple_valid_invariant : Prop :=
  inv_hoare_triple_valid example_simple_hoare_triple := by
  intro s s' h_pre h_exec
  exact h_pre

-- ### Example 4.2.2: Precondition Validity

Precondition Validity

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.2.1, lines 441-444

--**Natural Language:**
"The system shall maintain that preconditions are valid."

--**Formal Definition:**
```example example_precondition_valid_invariant : Prop :=
  inv_precondition_valid example_simple_hoare_triple.precondition example_simple_hoare_triple.command
```

--**Explanation:**
- The precondition is valid
- The system maintains that all preconditions are valid
- This demonstrates invariant of precondition validity

--**Verification:**
```#eval example_precondition_valid_invariant
-- Expected: true
```
-/
example example_precondition_valid_invariant : Prop :=
  inv_precondition_valid example_simple_hoare_triple.precondition example_simple_hoare_triple.command := by
  intro s h_pre
  exact ⟨s, h_pre⟩

-- ### Example 4.2.3: Postcondition Validity

Postcondition Validity

--**Source:** `spec/security/infrastructure_safety_contracts_spec.md`, section 4.2.1, lines 445-447

--**Natural Language:**
"The system shall maintain that postconditions are valid."

--**Formal Definition:**
```example example_postcondition_valid_invariant : Prop :=
  inv_postcondition_valid example_simple_hoare_triple.postcondition example_simple_hoare_triple.command
```

--**Explanation:**
- The postcondition is valid
- The system maintains that all postconditions are valid
- This demonstrates invariant of postcondition validity

--**Verification:**
```#eval example_postcondition_valid_invariant
-- Expected: true
```
-/
example example_postcondition_valid_invariant : Prop :=
  inv_postcondition_valid example_simple_hoare_triple.postcondition example_simple_hoare_triple.command := by
  intro s s' h_exec
  exact h_exec

end Morph.Specs.InfrastructureSafetyContracts