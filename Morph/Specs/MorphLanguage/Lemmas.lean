/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MorphLanguage.Spec

/-!
# MorphLanguage: real edits, and what the spec's theorems actually said

Research loop 13. Target: `Morph/Specs/MorphLanguage/`.

**What the loop found.** The module's *specification* is fine — it declares
`EditOperation`, `applyEdit`, `parseCode`, the dialect predicates and the
projectional-only mandate. Its *theorems* are true for the wrong reasons:

| Theorem | Why it was true |
|---|---|
| `applyEditToAst_id` | `applyEditToAst` **ignores its edit** — the parameter is `_edit` and the function returns `some ast` unconditionally. It is the identity by construction. |
| `parseCode_always_empty` | `parseCode` returns `some Program.empty` on *both* branches of its `if`. **It parses nothing.** |
| `applyEdit_insert` | `insert newCode => code ++ newCode` *appends*; it does not insert at a position. |
| `applyEdit_delete` | `delete => ""` *erases everything*; it does not delete a range. |
| `applyEdit_move` | `move _ _ => code` *does nothing*. |

So the language spec's editing and parsing operations are stubs, and the
theorems about them are true only because the stubs do nothing. This loop
replaces the editing operations with **real, position-aware** ones and proves
the properties that were previously vacuous.

**What is not fixed here.** `applyEditToAst` and `parseCode` remain stubs: the
real parser (`Morph/Frontend/Parser.lean`) is a *partial* recursive-descent
parser over a `Parser` structure, and connecting the specification to it needs
both a non-partial parser and a decision procedure for it — a separate piece of
work, named in §5 of the spec rather than faked here.
-/

namespace Morph.Specs.MorphLanguage

open Morph.Syntax

/-! ### Real edits

An edit is applied to a *source range*. Ranges are half-open `[lo, hi)`, and the
text is a list of characters — the list API is what makes the properties
provable, since `List.take`/`List.drop`/`List.length_append` all have clean
theorems (`String`'s `take`/`drop` return `String.Slice`, whose API is not). -/

/-- The half-open range `[lo, hi)` of a source text. -/
structure Range where
  /-- Start of the range (inclusive). -/
  lo : Nat
  /-- End of the range (exclusive). -/
  hi : Nat
  deriving Repr, BEq, DecidableEq

/-- A range is *well formed* when it is ordered. -/
def Range.WF (r : Range) : Prop := r.lo ≤ r.hi

/-- The text before the range. -/
def prefixOf (code : List Char) (r : Range) : List Char := code.take r.lo

/-- The text after the range. -/
def suffixOf (code : List Char) (r : Range) : List Char := code.drop r.hi

/-- The text inside the range. -/
def sliceOf (code : List Char) (r : Range) : List Char :=
  (code.drop r.lo).take (r.hi - r.lo)

/-- **Insert** `newCode` at position `pos`: the text before `pos` is kept, the
text after it is kept, and the new text goes *between* them. This is what the
specification's `insert` claimed and did not do — it appended. -/
def insertAt (code newCode : List Char) (pos : Nat) : List Char :=
  code.take pos ++ (newCode ++ code.drop pos)

/-- **Delete** the range `[lo, hi)`. The text before and after it is kept. This
is what the specification's `delete` claimed and did not do — it erased the
whole program. -/
def deleteRange (code : List Char) (r : Range) : List Char :=
  code.take r.lo ++ code.drop r.hi

/-- **Move** the range `[lo, hi)` to position `dst`: the moved text is removed
and re-inserted at `dst`. This is what the specification's `move` claimed and
did not do — it returned the code unchanged. -/
def moveRange (code : List Char) (r : Range) (dst : Nat) : List Char :=
  let moved := sliceOf code r
  let rest := deleteRange code r
  insertAt rest moved dst

/-- Taking a prefix of a concatenation, when the prefix ends inside the first
part. -/
private theorem take_append_prefix (a b : List Char) (n : Nat) (h : n ≤ a.length) :
    (a ++ b).take n = a.take n := by
  induction a generalizing n with
  | nil => simp at h; subst h; rfl
  | cons x a ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.cons_append, List.take_succ_cons]
          congr 1
          exact ih n (Nat.succ_le_succ_iff.mp h)

/-- Taking then dropping the same number of elements leaves nothing. -/
private theorem take_drop_self (l : List Char) (n : Nat) : (l.take n).drop n = [] := by
  induction l generalizing n with
  | nil => simp
  | cons x l ih =>
      cases n with
      | zero => rfl
      | succ n => simp only [List.take_succ_cons, List.drop_succ_cons]; exact ih n

/-- Dropping past the first part of a concatenation. -/
private theorem drop_append_prefix (a b : List Char) (n : Nat) (h : n ≤ a.length) :
    (a ++ b).drop n = a.drop n ++ b := by
  induction a generalizing n with
  | nil => simp at h; subst h; rfl
  | cons x a ih =>
      cases n with
      | zero => rfl
      | succ n => simp only [List.cons_append, List.drop_succ_cons]; exact ih n (Nat.succ_le_succ_iff.mp h)

/-! ### The theorems the specification's theorems should have been -/

/-- **Insertion puts the new text at the position**: the result is the old text
split at `pos` with the new text between. -/
theorem insertAt_split (code newCode : List Char) (pos : Nat) :
    insertAt code newCode pos = code.take pos ++ (newCode ++ code.drop pos) := rfl

/-- **Deletion removes exactly the range**: the result is the text before the
range followed by the text after it. -/
theorem deleteRange_split (code : List Char) (r : Range) :
    deleteRange code r = code.take r.lo ++ code.drop r.hi := rfl

/-- **Deletion preserves the prefix.** The text before the range is untouched. -/
theorem deleteRange_preserves_prefix (code : List Char) (r : Range) (h : r.lo ≤ code.length) :
    (deleteRange code r).take r.lo = code.take r.lo := by
  simp only [deleteRange]
  have hbound : r.lo ≤ (code.take r.lo).length := by
    simp only [List.length_take]
    omega
  rw [take_append_prefix (code.take r.lo) (code.drop r.hi) r.lo hbound]
  simp only [List.take_take, Nat.min_self]

/-- **Deletion preserves the suffix**, relative to the range's end. -/
theorem deleteRange_preserves_after (code : List Char) (r : Range) (h : r.lo ≤ code.length) :
    (deleteRange code r).drop r.lo = code.drop r.hi := by
  simp only [deleteRange]
  have hbound : r.lo ≤ (code.take r.lo).length := by
    simp only [List.length_take]
    omega
  rw [drop_append_prefix (code.take r.lo) (code.drop r.hi) r.lo hbound, take_drop_self]
  simp only [List.nil_append]

/-- **A move relocates the text**: the moved text is removed from its old place
and re-inserted at the destination. -/
theorem moveRange_split (code : List Char) (r : Range) (dst : Nat) :
    moveRange code r dst = (deleteRange code r).take dst ++ (sliceOf code r ++
      (deleteRange code r).drop dst) := by
  simp only [moveRange, insertAt]

/-- **An insert does not change the text before the insertion point.** -/
theorem insertAt_preserves_prefix (code newCode : List Char) (pos : Nat)
    (h : pos ≤ code.length) :
    (insertAt code newCode pos).take pos = code.take pos := by
  simp only [insertAt]
  have hbound : pos ≤ (code.take pos).length := by
    simp only [List.length_take]
    omega
  rw [take_append_prefix (code.take pos) (newCode ++ code.drop pos) pos hbound]
  simp only [List.take_take, Nat.min_self]

/-- **A delete of an empty range changes nothing.** -/
theorem deleteRange_empty (code : List Char) (lo hi : Nat) (h : lo = hi) :
    deleteRange code ⟨lo, hi⟩ = code := by
  simp [deleteRange, h]

/-- The specification's `delete` erased the whole program; the real one removes
a range and keeps the rest. This is the difference the stub made. -/
example : deleteRange "hello world".toList ⟨0, 5⟩ = " world".toList := by decide

/-- The specification's `insert` appended; the real one inserts at a position. -/
example : insertAt "hello".toList "say ".toList 0 = "say hello".toList := by decide

/-! ### The stubs, stated precisely

The following are the properties the specification's theorems *claimed*; they
hold only because the operations are stubs. They are recorded here so that the
gap is explicit rather than hidden behind a `rfl`. -/

/-- The specification's `parseCode` returns the empty program for every input,
including non-empty ones: it parses nothing. -/
theorem parseCode_is_a_stub (code : String) :
    Morph.Specs.MorphLanguage.parseCode code = some Morph.Syntax.Program.empty := by
  simp [Morph.Specs.MorphLanguage.parseCode]

/-- The specification's `applyEditToAst` ignores its edit: it is the identity
on programs. -/
theorem applyEditToAst_is_a_stub (ast : Morph.Syntax.Program)
    (edit : Morph.Specs.MorphLanguage.EditOperation) :
    Morph.Specs.MorphLanguage.applyEditToAst ast edit = some ast := by
  rfl

end Morph.Specs.MorphLanguage
