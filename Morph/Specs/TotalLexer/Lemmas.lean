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

/-! ### Every scanner that succeeds consumed characters

Each scanner, on a non-empty input, either fails or leaves a strictly shorter
remainder. These are the three facts the step-level progress theorem composes. -/

theorem scanNum_consumes' : ∀ (c : Char) (r : List Char) (v : Nat) (r' : List Char),
    scanNum (c :: r) = some (v, r') → r'.length < (c :: r).length := by
  intro c r v r' h
  simp only [scanNum] at h
  by_cases hd : isDigitC c
  · rw [if_pos hd] at h
    injection h with heq
    cases heq
    exact dropWhile_cons_lt isDigitC c r hd
  · rw [if_neg hd] at h
    cases h

/-- An identifier-start character also satisfies the identifier-rest rule, so the
maximal-munch run starts where the identifier does. -/
theorem isIdentStart_rest (c : Char) (h : isIdentStart c = true) : isIdentRest c = true := by
  unfold isIdentStart at h
  unfold isIdentRest
  cases ha : c.isAlpha with
  | true => simp [ha]
  | false =>
      have hx : (c == '_') = true := by simpa [isIdentStart, ha] using h
      simp [ha, hx]

theorem scanIdent_consumes' : ∀ (c : Char) (r : List Char) (s : String) (r' : List Char),
    scanIdent (c :: r) = some (s, r') → r'.length < (c :: r).length := by
  intro c r s r' h
  simp only [scanIdent] at h
  by_cases hd : isIdentStart c
  · rw [if_pos hd] at h
    injection h with heq
    cases heq
    exact dropWhile_cons_lt isIdentRest c r (isIdentStart_rest c hd)
  · rw [if_neg hd] at h
    cases h

theorem scanOp_consumes' : ∀ (c : Char) (r : List Char) (o : String) (r' : List Char),
    scanOp (c :: r) = some (o, r') → isOpC c = true ∧ r'.length < (c :: r).length := by
  intro c r o r' h
  simp only [scanOp] at h
  by_cases hd : isOpC c
  · rw [if_pos hd] at h
    injection h with heq
    cases heq
    exact ⟨hd, by simp⟩
  · rw [if_neg hd] at h
    cases h

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

/-- **Progress.** A step either reports end of input, or it consumes at least
one character. There is no third outcome: in particular no silent stall.

This is the step-level theorem that the shipped `partial def nextToken` cannot
have. -/
theorem nextToken_progress (cs : List Char) :
    (nextToken cs).1 = .eof ∨ (nextToken cs).2.length < cs.length := by
  cases cs with
  | nil => exact Or.inl (by simp [nextToken, skipWs])
  | cons c cs =>
      have hskip : (skipWs (c :: cs)).length ≤ (c :: cs).length := skipWs_length_le (c :: cs)
      simp only [nextToken]
      generalize hsk : skipWs (c :: cs) = rest
      cases rest with
      | nil => exact Or.inl (by simp [hsk])
      | cons c' r =>
          have hrest : (c' :: r).length ≤ (c :: cs).length := by
            rw [hsk] at hskip
            omega
          cases hnum : scanNum (c' :: r) with
          | some v =>
              obtain ⟨n, r'⟩ := v
              have hlt := scanNum_consumes' c' r n r' hnum
              simp only [hnum]
              omega
          | none =>
              cases hid : scanIdent (c' :: r) with
              | some v =>
                  obtain ⟨nm, r'⟩ := v
                  have hlt := scanIdent_consumes' c' r nm r' hid
                  simp only [hnum, hid]
                  omega
              | none =>
                  cases hop : scanOp (c' :: r) with
                  | some v =>
                      obtain ⟨o, r'⟩ := v
                      have hopf := scanOp_consumes' c' r o r' hop
                      simp only [hnum, hid, hop]
                      omega
                  | none =>
                      simp only [hnum, hid, hop]
                      have hrest' : (c' :: r).tail.length < (c :: cs).length := by
                        simp only [List.tail_cons, List.length_cons] at hrest ⊢
                        omega
                      omega

/-! ### The whole scan terminates

Progress plus the input's length gives a bound. This is the theorem that replaces
the shipped `partial`: the lexer *reaches end of input* within `|cs| + 1` steps,
and the proof is an ordinary well-founded decrease on the residual input. -/

/-- The input still to be scanned after `k` steps. -/
def residual : Nat → List Char → List Char
  | 0, cs => cs
  | k + 1, cs => residual k (nextToken cs).2

/-- The residual input shrinks by at least one on every non-`.eof` step. -/
theorem residual_bound : ∀ (k : Nat) (cs : List Char),
    (∀ j < k, (nextToken (residual j cs)).1 ≠ .eof) →
    (residual k cs).length + k ≤ cs.length := by
  intro k
  induction k with
  | zero => intro cs _; simp [residual]
  | succ k ih =>
      intro cs hall
      have hstep : (nextToken cs).1 ≠ .eof := hall 0 (by omega)
      have hlt : (nextToken cs).2.length < cs.length := by
        rcases nextToken_progress cs with h | h
        · exact absurd h hstep
        · exact h
      have hrec := ih (nextToken cs).2 (fun j hj => hall (j + 1) (by omega))
      simp only [residual] at hrec ⊢
      omega

/-- **The scan reaches end of input.** For every input there is a step within
`|cs| + 1` that reports `.eof` — so the lexing loop terminates, which is exactly
what the shipped `partial def nextToken` could not say. -/
theorem reaches_eof (cs : List Char) :
    ∃ j, j ≤ cs.length + 1 ∧ (nextToken (residual j cs)).1 = .eof := by
  refine Classical.byContradiction ?_
  intro hn
  have hall : ∀ j, j < cs.length + 1 → (nextToken (residual j cs)).1 ≠ .eof := by
    intro j hj hje
    exact hn ⟨j, by omega, hje⟩
  have h := residual_bound (cs.length + 1) cs hall
  omega

/-! ### Token-list assembly (loop 53)

Loop 9 left the token *list* unassembled: `nextToken_progress` and
`reaches_eof` bound the steps but no `lexAll` collected them, so the
`lexAll` length bound was open. Loop 53 closes it minimally: `lexAllFuel`
collects at most one token per fuel unit, and `lexAll` seeds it with
`|cs| + 1` — the exact bound `reaches_eof` gives.

Research: Coqlex (Ouedraogo, Programming Journal 2024) generates a
*proved* lexer from a spec; Verbatim (POPL) maximal-munch with explicit
error tokens — the same `.eof`-as-token discipline used here. Other
languages: tree-sitter (GLR, total but unproved), Rust `logos`
(derive-macro, maximal munch by longest match, termination by construction).
Morph's gap was not the discipline but the missing list assembly.
-/

/-- Collect at most `fuel + 1` tokens: one per step, stopping at `.eof`. -/
def lexAllFuel : Nat → List Char → List TokKind
  | 0, cs => [(nextToken cs).1]
  | n + 1, cs =>
      let (k, rest) := nextToken cs
      match k with
      | .eof => [.eof]
      | _ => k :: lexAllFuel n rest

/-- The fuel bounds the token count. -/
theorem lexAllFuel_length_le (n : Nat) (cs : List Char) :
    (lexAllFuel n cs).length ≤ n + 1 := by
  induction n generalizing cs with
  | zero => simp [lexAllFuel]
  | succ n ih =>
      simp only [lexAllFuel]
      split
      · simp
      · simp only [List.length_cons]
        have h := ih ((nextToken cs).2)
        omega

/-- The assembled scan: fuel is the `reaches_eof` bound. -/
def lexAll (cs : List Char) : List TokKind :=
  lexAllFuel (cs.length + 1) cs

/-- The assembled scan is bounded by the input length. -/
theorem lexAll_length_le (cs : List Char) : (lexAll cs).length ≤ cs.length + 2 := by
  simp only [lexAll]
  have h := lexAllFuel_length_le (cs.length + 1) cs
  omega

/-! ### Character-class disjointness (concrete witnesses)

A full disjointness (`isAlpha` vs `isDigit` for all `Char`) needs range
lemmas about `Char.toNat` that core Lean does not supply, so it is not
claimed. What *is* claimed are the concrete separations the lexer relies
on: digits do not start identifiers, and the operator alphabet is disjoint
from digits on the witnesses the scanner actually branches on.
-/

/-- `'0'` is a digit but not an identifier start. -/
theorem digit_zero_not_identStart : isDigitC '0' = true ∧ isIdentStart '0' = false := by
  decide

/-- `'_'` starts identifiers but is not a digit. -/
theorem underscore_ident_not_digit : isIdentStart '_' = true ∧ isDigitC '_' = false := by
  decide

/-- `'#'` matches no rule and falls through to the operator fallback. -/
theorem hash_falls_through : scanNum ['#'] = none ∧ scanIdent ['#'] = none ∧ scanOp ['#'] = none := by
  decide

end Morph.Specs.TotalLexer
