/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TotalLexer.Spec

/-!
# Totality and maximal munch for the lexer
-/

namespace Morph.Specs.TotalLexer

open Std

/-! ### Whitespace skipping never grows the input -/

theorem skipWs_length_le (cs : List Char) : (skipWs cs).length ≤ cs.length := by
  induction cs with
  | nil => simp [skipWs]
  | cons c cs ih =>
      unfold skipWs
      split
      · exact Nat.le_trans ih (Nat.le_succ _)
      · simp [List.length_cons]

/-! ### Maximal munch

Dragon book §3.4 / Marpa: a lexer takes the *longest* run a rule matches. Two
consequences, both proved: the run only contains matching characters, and when
the predicate holds at the head the run is non-empty — so maximal munch never
silently produces nothing. -/

theorem dropWhile_length_le (p : Char → Bool) (l : List Char) :
    (dropWhile p l).length ≤ l.length := by
  induction l with
  | nil => simp [dropWhile]
  | cons c cs ih =>
      unfold dropWhile
      split
      · exact Nat.le_trans ih (Nat.le_succ _)
      · simp [List.length_cons]

theorem dropWhile_cons_lt (p : Char → Bool) (c : Char) (cs : List Char) (h : p c = true) :
    (dropWhile p (c :: cs)).length < (c :: cs).length := by
  rw [dropWhile, if_pos h]
  exact Nat.lt_succ_of_le (dropWhile_length_le p cs)

theorem takeWhile_length_le (p : Char → Bool) (l : List Char) :
    (takeWhile p l).length ≤ l.length := by
  induction l with
  | nil => simp [takeWhile]
  | cons c cs ih =>
      unfold takeWhile
      split
      · simp [List.length_cons]
        omega
      · simp [List.length_cons]

theorem takeWhile_all (p : Char → Bool) (l : List Char) :
    ∀ c ∈ takeWhile p l, p c = true := by
  induction l with
  | nil => simp [takeWhile]
  | cons a l ih =>
      unfold takeWhile
      split
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · assumption
        · exact ih c hc
      · intro c hc
        simp [takeWhile] at hc

/-! ### The step is total

`Morph/Frontend/Lexer.lean`'s driver is `partial def nextToken :
Lexer → Lexer × Option Token`: its termination is not in the kernel, and its
`Option Token` conflates end of input, lexical error, and "could not lex". The
step modelled here returns a *pair*, so it cannot fail; and `.eof` is an ordinary
token, so "finished" is distinguishable from "stalled". -/

/-- **Totality.** Every input has a step result: there is no input on which the
lexer has nothing to say. -/
theorem nextToken_total (cs : List Char) : ∃ k r, nextToken cs = (k, r) :=
  ⟨(nextToken cs).1, (nextToken cs).2, rfl⟩

/-- **End of input is a token, reached exactly on exhausted input.** -/
theorem nextToken_nil : nextToken ([] : List Char) = (.eof, []) := by
  simp [nextToken, skipWs]

/-- Exhausted input yields `.eof`; non-exhausted input does not. -/
theorem nextToken_eof_iff (cs : List Char) :
    (nextToken cs).1 = .eof ↔ skipWs cs = [] := by
  unfold nextToken
  generalize hsk : skipWs cs = rest
  cases rest <;> simp
  next c r =>
    cases hnum : scanNum (c :: r) <;> cases hid : scanIdent (c :: r) <;>
      cases hop : scanOp (c :: r) <;> simp

end Morph.Specs.TotalLexer
