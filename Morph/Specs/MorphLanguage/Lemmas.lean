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

**Loop 32.** The four `Prop := True` claims at the end of the spec were made
real: `min` is canonical, `hum` transient, every `ErrorResult` is either an `ok`
or an error carrying a file/line/column.

**Loop 46 closed the remaining stubs.** `parseCode` now delegates to the shipped
*total* frontend parser (`Morph.Frontend.parse`), `applyEditToAst` dispatches
the four edits for real (`replace`/`insert` re-parse, `delete` clears, `move`
reorders statements), and `renderCode` renders programs in both dialects. The
old vacuous claims are replaced by:

- `parseCode_isSome_iff` — parsing succeeds exactly when the frontend accepts
  the text; `parseCode_malformed` — `"("` is rejected.
- `projectionalOnlyMandate_refuted` and `projectional_only_mandate_refuted` —
  "every string parses" and "every edit succeeds" are **false** for a real
  parser, and the witnesses prove it. What a projectional editor guarantees is
  that *accepted* edits go through the AST, not that arbitrary text parses.
- `applyEditToAst_delete`/`_replace`/`_insert`/`_move` — the four edit cases;
  `applyEditToAst_insert_malformed` — a malformed insert fails rather than
  silently succeeding.
- `moveStmt_out_of_range`/`moveStmt_length`/`moveStmt_singleton` — the
  reordering primitive is total and length-preserving.
- `renderCode_min_empty`/`renderCode_hum_empty` plus native-decided examples —
  rendering is real and dialect-sensitive.
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

/-! ### The parser adapter, characterised

`parseCode` is a thin wrapper around `Morph.Frontend.parse`: it wraps the parsed
expression as a one-statement program and turns a parse error into `none`. -/

/-- **Parsing succeeds exactly when the frontend accepts the text.** -/
theorem parseCode_isSome_iff (code : String) :
    (parseCode code).isSome = true ↔ ∃ e, Morph.Frontend.parse code = .ok e := by
  unfold parseCode
  cases h : Morph.Frontend.parse code with
  | ok e => simp
  | error err => simp

/-- **On an accepted input the result is the wrapped expression.** -/
theorem parseCode_ok (code : String) (e : Expr)
    (h : Morph.Frontend.parse code = .ok e) :
    parseCode code = some { stmts := [.exprStmt e] } := by
  unfold parseCode
  rw [h]

/-- **Malformed input is rejected.** `"("` is an unbalanced parenthesis; the
frontend parser returns an error for it, so `parseCode` returns `none`. -/
theorem parseCode_malformed : (parseCode "(").isNone = true := by native_decide

/-- **The projectional-only mandate is false as stated.** It claims every source
string parses; `"("` does not. (Recorded as a refutation, not deleted, so the
false law stays visible.) -/
theorem projectionalOnlyMandate_refuted : ¬ projectionalOnlyMandate := by
  intro h
  have h1 := h "("
  have h2 : (parseCode "(").isSome = false := by native_decide
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-! ### AST edits

`applyEditToAst` is now a real dispatcher. Each case has its defining equation;
the interesting content is that `delete`/`move` cannot fail, while
`replace`/`insert` fail exactly when their text fails to parse. -/

theorem applyEditToAst_delete (ast : Morph.Syntax.Program) :
    applyEditToAst ast EditOperation.delete = some Morph.Syntax.Program.empty := rfl

theorem applyEditToAst_replace (ast : Morph.Syntax.Program) (src : String) :
    applyEditToAst ast (EditOperation.replace src) = parseCode src := rfl

theorem applyEditToAst_insert (ast : Morph.Syntax.Program) (src : String) :
    applyEditToAst ast (EditOperation.insert src) =
      (parseCode src).map (fun p => { stmts := ast.stmts ++ p.stmts }) := rfl

theorem applyEditToAst_move (ast : Morph.Syntax.Program) (i j : Nat) :
    applyEditToAst ast (EditOperation.move i j) =
      some { stmts := moveStmt i j ast.stmts } := rfl

/-- `delete` always succeeds. -/
theorem applyEditToAst_delete_isSome (ast : Morph.Syntax.Program) :
    (applyEditToAst ast EditOperation.delete).isSome = true := rfl

/-- `move` always succeeds. -/
theorem applyEditToAst_move_isSome (ast : Morph.Syntax.Program) (i j : Nat) :
    (applyEditToAst ast (EditOperation.move i j)).isSome = true := rfl

/-- A malformed `insert` fails: the edit is not silently accepted. -/
theorem applyEditToAst_insert_malformed :
    (applyEditToAst Morph.Syntax.Program.empty (EditOperation.insert "(")).isNone = true := by
  native_decide

/-- **"Every edit yields a program" is false**: a malformed `insert` yields
`none`. The true statement is per-case (`_delete_isSome`, `_move_isSome`, and
`_replace`/`_insert` conditional on parsing). -/
theorem projectional_only_mandate_refuted : ¬ projectional_only_mandate := by
  intro h
  have h1 := h Morph.Syntax.Program.empty (EditOperation.insert "(")
  have h2 : (applyEditToAst Morph.Syntax.Program.empty
      (EditOperation.insert "(")).isSome = false := by native_decide
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-! ### Statement reordering

`moveStmt i j xs` removes statement `i` and re-inserts it at position `j`. It is
total: an out-of-range source index is a no-op, and a destination past the end
appends. -/

/-- An out-of-range source index leaves the statement list unchanged. -/
theorem moveStmt_out_of_range (i j : Nat) (xs : List Stmt) (h : xs[i]? = none) :
    moveStmt i j xs = xs := by
  unfold moveStmt
  rw [h]

/-- **A move preserves the number of statements.** -/
theorem moveStmt_length (i j : Nat) (xs : List Stmt) (h : i < xs.length) :
    (moveStmt i j xs).length = xs.length := by
  unfold moveStmt
  split
  · next hnone =>
      have := List.getElem?_eq_none_iff.mp hnone
      omega
  · next x _ =>
      simp only [List.length_append, List.length_cons, List.length_take,
        List.length_drop, List.length_eraseIdx_of_lt h]
      omega

/-- A singleton is unchanged by a move. -/
theorem moveStmt_singleton (j : Nat) (s : Stmt) :
    moveStmt 0 j [s] = [s] := by
  unfold moveStmt
  simp

/-! ### Rendering

`renderCode` used to return `""` for every program. It now renders statements
in either dialect; `hum` puts spaces around binary operators and separates
statements with `;\n`, `min` is compact. The empty-program facts are proved by
`rfl`; the concrete renderings are checked by evaluation (the renderers are
mutually recursive, so the kernel does not reduce them definitionally). -/

theorem renderCode_min_empty :
    renderCode Morph.Syntax.Program.empty Dialect.min = "" := rfl

theorem renderCode_hum_empty :
    renderCode Morph.Syntax.Program.empty Dialect.hum = "" := rfl

/-- `min` renders compactly. -/
example : renderCode { stmts := [.exprStmt (.binop .add (.lit (.int 1)) (.lit (.int 2)))] }
    Dialect.min = "(1+2)" := by native_decide

/-- `hum` spaces binary operators. -/
example : renderCode { stmts := [.exprStmt (.binop .add (.lit (.int 1)) (.lit (.int 2)))] }
    Dialect.hum = "(1 + 2)" := by native_decide

/-- Declarations render with their type annotation. -/
example : renderCode { stmts := [.varDecl ⟨"x"⟩ .intType (.lit (.int 5))] }
    Dialect.min = "let x: int = 5" := by native_decide

/-! ### The remaining spec claims, proved -/

theorem min_is_canonical_holds : min_is_canonical := by
  unfold min_is_canonical isCanonicalDialect; rfl

theorem hum_is_transient_holds : hum_is_transient := by
  unfold hum_is_transient isTransientDialect; rfl

theorem error_handling_explicit_holds : error_handling_explicit := by
  intro α r
  cases r with
  | ok a => exact Or.inl ⟨a, rfl⟩
  | error e => exact Or.inr ⟨e, rfl⟩

end Morph.Specs.MorphLanguage
