/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Syntax

namespace Morph.Frontend.NameResolution

open Morph.Syntax

/-!
# Name Resolution — its own pass (loop 82)

The parser used to own resolution inline (`resolveIdent` + a `scope`
threaded through every `parse*` function): a bound name becomes its de
Bruijn index, an unbound name stays free (loop 72 — without this, `let x
= 5 in x + 1` evaluated to `stuck`, not `6`, because the evaluator binds
`bvar`s via `Context.pushBv`).

This module factors that discipline out so it can be stated and proved
once:

- `resolveIdent`: the single-occurrence decision (moved here unchanged;
  `Parser.parseIdentifier` calls it);
- `resolveExpr` / `resolveExprList` / `resolveExprArms`: the structural
  pass — `fvar`s in `scope` become `bvar`s, everything else recurses.
  The scope is extended exactly where the parser extends it:
  **nowhere**, except `match_` arms, whose pattern names survive in the
  tree (`patVars`). Every other binder is anonymous in `Expr` (`lam n`,
  `let_`'s single slot, `forLoop`'s iterator — which the parser
  deliberately parses in the *same* scope, loop 78b), so no name can
  reach those slots and the scope passes through unchanged.

`Expr` is a nested inductive (`List Expr` fields), so — like
`liftUnder`/`boundCount` and their `..._list`/`..._arms` companions —
definitions and proofs go in `mutual` blocks, not through the
`induction` tactic.

Proved below: the occurrence decision fires exactly on membership
(`resolveIdent_self`, `resolveIdent_of_mem`, `resolveIdent_of_not_mem`),
the pass is a projection (`resolveExpr_idem` — parser output is
stable), and name-free trees are fixed points
(`resolveExpr_closed`).
-/

/-- Resolve one identifier against the scope (innermost binder first). -/
def resolveIdent (scope : List String) (name : String) : Expr :=
  match scope.findIdx? (· == name) with
  | some i => .bvar i
  | none => .fvar name

/-- The head of the scope resolves to index 0 (innermost wins). -/
theorem resolveIdent_self (x : String) (s : List String) :
    resolveIdent (x :: s) x = .bvar 0 := by
  simp [resolveIdent, List.findIdx?_cons]

/-- Membership in the scope is exactly what makes `findIdx?` fire. -/
theorem mem_of_findIdx?_eq_some {l : List String} {x : String} {i : Nat}
    (h : l.findIdx? (· == x) = some i) : x ∈ l := by
  induction l generalizing i with
  | nil => simp [List.findIdx?_nil] at h
  | cons hd tl ih =>
    match hbx : (hd == x) with
    | true =>
      have hdx : hd = x := by simpa using hbx
      subst hdx
      exact List.mem_cons_self
    | false =>
      have hcons : (hd :: tl).findIdx? (· == x) =
          (tl.findIdx? (· == x)).map (· + 1) := by
        simp [List.findIdx?_cons, hbx]
      rw [hcons] at h
      match htl : tl.findIdx? (· == x) with
      | some j => exact List.mem_cons_of_mem _ (ih htl)
      | none => simp [htl] at h

/-- Non-membership makes `findIdx?` miss. -/
theorem findIdx?_eq_none_of_not_mem {l : List String} {x : String}
    (h : x ∉ l) : l.findIdx? (· == x) = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd ≠ x := by
      intro heq
      subst heq
      exact h List.mem_cons_self
    have htl : x ∉ tl := fun hm => h (List.mem_cons_of_mem _ hm)
    have hbx : (hd == x) = false := by
      match hbb : (hd == x) with
      | true =>
        have hdx : hd = x := by simpa using hbb
        exact absurd hdx hhd
      | false => rfl
    simp [List.findIdx?_cons, hbx, ih htl]

/-- Membership makes `findIdx?` hit at some index. -/
theorem findIdx?_eq_some_of_mem {l : List String} {x : String}
    (h : x ∈ l) : ∃ i, l.findIdx? (· == x) = some i := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    match hbx : (hd == x) with
    | true =>
      exact ⟨0, by simp [List.findIdx?_cons, hbx]⟩
    | false =>
      have hne : hd ≠ x := by
        intro heq
        subst heq
        simp at hbx
      have htl : x ∈ tl := by
        rcases List.mem_cons.mp h with rfl | hm
        · exact absurd rfl hne
        · exact hm
      obtain ⟨i, hi⟩ := ih htl
      exact ⟨i + 1, by simp [List.findIdx?_cons, hbx, hi]⟩

/-- A name in scope becomes *some* de Bruijn index. -/
theorem resolveIdent_of_mem {scope : List String} {x : String}
    (h : x ∈ scope) : ∃ i, resolveIdent scope x = .bvar i := by
  obtain ⟨i, hi⟩ := findIdx?_eq_some_of_mem h
  exact ⟨i, by simp [resolveIdent, hi]⟩

/-- A name outside the scope stays free. -/
theorem resolveIdent_of_not_mem {scope : List String} {x : String}
    (h : x ∉ scope) : resolveIdent scope x = .fvar x := by
  simp [resolveIdent, findIdx?_eq_none_of_not_mem h]

/-! ## The structural pass -/

mutual

/-- Convert in-scope `fvar`s to `bvar`s.

Scope extensions mirror the parser exactly: `let_` initialisers parse
in the outer scope and bodies in `name :: scope` — but the name is gone
from the tree (anonymous slot), so both sides here see the *caller*'s
scope; only `match_` arms carry their binder names (`patVars`) into the
body. `forLoop` bodies parse in the same scope (loop 78b). -/
def resolveExpr : List String → Expr → Expr
  | _, .bvar n => .bvar n
  | scope, .fvar x => resolveIdent scope x
  | _, .lit v => .lit v
  | scope, .unop op e => .unop op (resolveExpr scope e)
  | scope, .binop op a b => .binop op (resolveExpr scope a) (resolveExpr scope b)
  | scope, .app f args => .app (resolveExpr scope f) (resolveExprList scope args)
  | scope, .lam n body => .lam n (resolveExpr scope body)
  | scope, .let_ init body => .let_ (resolveExpr scope init) (resolveExpr scope body)
  | scope, .ifThenElse c t f =>
    .ifThenElse (resolveExpr scope c) (resolveExpr scope t) (resolveExpr scope f)
  | scope, .forLoop s e body =>
    .forLoop (resolveExpr scope s) (resolveExpr scope e) (resolveExprList scope body)
  | scope, .block es => .block (resolveExprList scope es)
  | scope, .match_ scrut arms =>
    .match_ (resolveExpr scope scrut) (resolveExprArms scope arms)
  | scope, .field_ e name => .field_ (resolveExpr scope e) name
  | scope, .pipe e f => .pipe (resolveExpr scope e) (resolveExpr scope f)
  | scope, .typeAsc e τ => .typeAsc (resolveExpr scope e) τ
  | scope, .some_ e => .some_ (resolveExpr scope e)
  | _, .none_ => .none_
  | scope, .ok_ e => .ok_ (resolveExpr scope e)
  | scope, .err_ e => .err_ (resolveExpr scope e)
  | scope, .nullCoalesce a b =>
    .nullCoalesce (resolveExpr scope a) (resolveExpr scope b)
  | scope, .tuple_ es => .tuple_ (resolveExprList scope es)
  | scope, .arrayLit es => .arrayLit (resolveExprList scope es)
  | scope, .arrayIndex a i => .arrayIndex (resolveExpr scope a) (resolveExpr scope i)
  | scope, .refCreate e c τ => .refCreate (resolveExpr scope e) c τ
  | scope, .refLoad e => .refLoad (resolveExpr scope e)
  | scope, .refStore r v τ => .refStore (resolveExpr scope r) (resolveExpr scope v) τ
  | scope, .refFree e => .refFree (resolveExpr scope e)
  | scope, .refCast e c => .refCast (resolveExpr scope e) c

/-- `resolveExpr` over an expression list. -/
def resolveExprList : List String → List Expr → List Expr
  | _, [] => []
  | scope, e :: es => resolveExpr scope e :: resolveExprList scope es

/-- `resolveExpr` over match arms; bodies see the pattern's binders. -/
def resolveExprArms : List String → List (Pattern × Expr) → List (Pattern × Expr)
  | _, [] => []
  | scope, (pat, body) :: rest =>
    (pat, resolveExpr (patVars pat ++ scope) body) :: resolveExprArms scope rest

end

/-- Bound variables pass through untouched. -/
theorem resolveExpr_bvar (scope : List String) (n : Nat) :
    resolveExpr scope (.bvar n) = .bvar n := rfl

/-- One occurrence is already stable: resolving its outcome changes nothing. -/
theorem resolveIdent_stable (scope : List String) (x : String) :
    resolveExpr scope (resolveIdent scope x) = resolveIdent scope x := by
  by_cases h : x ∈ scope
  · obtain ⟨j, hj⟩ := resolveIdent_of_mem h
    rw [hj]; rfl
  · simp [resolveExpr, resolveIdent_of_not_mem h]

/-! ## The pass is a projection -/

mutual

/-- Re-resolving changes nothing on expression lists. -/
theorem resolveExpr_idem_list : forall (scope : List String) (es : List Expr),
    resolveExprList scope (resolveExprList scope es) = resolveExprList scope es
  | _, [] => rfl
  | scope, hd :: tl => by
    simp only [resolveExprList, resolveExpr_idem scope hd,
      resolveExpr_idem_list scope tl]

/-- Re-resolving changes nothing on arm lists. -/
theorem resolveExpr_idem_arms : forall (scope : List String)
    (arms : List (Pattern × Expr)),
    resolveExprArms scope (resolveExprArms scope arms) = resolveExprArms scope arms
  | _, [] => rfl
  | scope, (pat, body) :: rest => by
    simp only [resolveExprArms,
      resolveExpr_idem (patVars pat ++ scope) body,
      resolveExpr_idem_arms scope rest]

/-- The pass is a projection: parser output is stable under re-resolution. -/
theorem resolveExpr_idem : forall (scope : List String) (e : Expr),
    resolveExpr scope (resolveExpr scope e) = resolveExpr scope e
  | _, .bvar n => rfl
  | scope, .fvar x => resolveIdent_stable scope x
  | _, .lit v => rfl
  | scope, .unop op e => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .binop op a b => by
    simp [resolveExpr, resolveExpr_idem scope a, resolveExpr_idem scope b]
  | scope, .app f args => by
    simp only [resolveExpr, resolveExpr_idem scope f,
      resolveExpr_idem_list scope args]
  | scope, .lam n body => by simp [resolveExpr, resolveExpr_idem scope body]
  | scope, .let_ init body => by
    simp [resolveExpr, resolveExpr_idem scope init, resolveExpr_idem scope body]
  | scope, .ifThenElse c t f => by
    simp only [resolveExpr, resolveExpr_idem scope c, resolveExpr_idem scope t,
      resolveExpr_idem scope f]
  | scope, .forLoop s e body => by
    simp only [resolveExpr, resolveExpr_idem scope s, resolveExpr_idem scope e,
      resolveExpr_idem_list scope body]
  | scope, .block es => by
    simp only [resolveExpr, resolveExpr_idem_list scope es]
  | scope, .match_ scrut arms => by
    simp only [resolveExpr, resolveExpr_idem scope scrut,
      resolveExpr_idem_arms scope arms]
  | scope, .field_ e name => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .pipe e f => by
    simp [resolveExpr, resolveExpr_idem scope e, resolveExpr_idem scope f]
  | scope, .typeAsc e τ => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .some_ e => by simp [resolveExpr, resolveExpr_idem scope e]
  | _, .none_ => rfl
  | scope, .ok_ e => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .err_ e => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .nullCoalesce a b => by
    simp [resolveExpr, resolveExpr_idem scope a, resolveExpr_idem scope b]
  | scope, .tuple_ es => by
    simp only [resolveExpr, resolveExpr_idem_list scope es]
  | scope, .arrayLit es => by
    simp only [resolveExpr, resolveExpr_idem_list scope es]
  | scope, .arrayIndex a i => by
    simp [resolveExpr, resolveExpr_idem scope a, resolveExpr_idem scope i]
  | scope, .refCreate e c τ => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .refLoad e => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .refStore r v τ => by
    simp [resolveExpr, resolveExpr_idem scope r, resolveExpr_idem scope v]
  | scope, .refFree e => by simp [resolveExpr, resolveExpr_idem scope e]
  | scope, .refCast e c => by simp [resolveExpr, resolveExpr_idem scope e]

end

/-! ## Name-free trees are fixed points -/

mutual

/-- Whether an expression mentions any free variable by name. -/
def hasFVar : Expr → Bool
  | .bvar _ => false
  | .fvar _ => true
  | .lit _ => false
  | .unop _ e => hasFVar e
  | .binop _ a b => hasFVar a || hasFVar b
  | .app f args => hasFVar f || hasFVarList args
  | .lam _ body => hasFVar body
  | .let_ init body => hasFVar init || hasFVar body
  | .ifThenElse c t f => hasFVar c || hasFVar t || hasFVar f
  | .forLoop s e body => hasFVar s || hasFVar e || hasFVarList body
  | .block es => hasFVarList es
  | .match_ scrut arms => hasFVar scrut || hasFVarArms arms
  | .field_ e _ => hasFVar e
  | .pipe e f => hasFVar e || hasFVar f
  | .typeAsc e _ => hasFVar e
  | .some_ e => hasFVar e
  | .none_ => false
  | .ok_ e => hasFVar e
  | .err_ e => hasFVar e
  | .nullCoalesce a b => hasFVar a || hasFVar b
  | .tuple_ es => hasFVarList es
  | .arrayLit es => hasFVarList es
  | .arrayIndex a i => hasFVar a || hasFVar i
  | .refCreate e _ _ => hasFVar e
  | .refLoad e => hasFVar e
  | .refStore r v _ => hasFVar r || hasFVar v
  | .refFree e => hasFVar e
  | .refCast e _ => hasFVar e

/-- `hasFVar` over an expression list. -/
def hasFVarList : List Expr → Bool
  | [] => false
  | e :: es => hasFVar e || hasFVarList es

/-- `hasFVar` over match-arm bodies. -/
def hasFVarArms : List (Pattern × Expr) → Bool
  | [] => false
  | (_, body) :: rest => hasFVar body || hasFVarArms rest

end

mutual

/-- Name-free lists resolve to themselves. -/
theorem resolveExpr_closed_list : forall (scope : List String) (es : List Expr),
    hasFVarList es = false → resolveExprList scope es = es
  | _, [], _ => rfl
  | scope, hd :: tl, h => by
    simp only [hasFVarList, Bool.or_eq_false_iff] at h
    simp [resolveExprList, resolveExpr_closed scope hd h.1,
      resolveExpr_closed_list scope tl h.2]

/-- Name-free arm bodies resolve to themselves. -/
theorem resolveExpr_closed_arms : forall (scope : List String)
    (arms : List (Pattern × Expr)),
    hasFVarArms arms = false → resolveExprArms scope arms = arms
  | _, [], _ => rfl
  | scope, (pat, body) :: rest, h => by
    simp only [hasFVarArms, Bool.or_eq_false_iff] at h
    simp [resolveExprArms, resolveExpr_closed (patVars pat ++ scope) body h.1,
      resolveExpr_closed_arms scope rest h.2]

/-- Name-free trees are fixed points at any scope: nothing to convert. -/
theorem resolveExpr_closed : forall (scope : List String) (e : Expr),
    hasFVar e = false → resolveExpr scope e = e
  | _, .bvar n, _ => rfl
  | _, .fvar x, h => by simp [hasFVar] at h
  | _, .lit v, _ => rfl
  | scope, .unop op e, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .binop op a b, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope a h.1, resolveExpr_closed scope b h.2⟩
  | scope, .app f args, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope f h.1, resolveExpr_closed_list scope args h.2⟩
  | scope, .lam n body, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope body h
  | scope, .let_ init body, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope init h.1, resolveExpr_closed scope body h.2⟩
  | scope, .ifThenElse c t f, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    obtain ⟨⟨hc, ht⟩, hf⟩ := h
    simp only [resolveExpr, resolveExpr_closed scope c hc,
      resolveExpr_closed scope t ht, resolveExpr_closed scope f hf]
  | scope, .forLoop s e body, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    obtain ⟨⟨hs, he⟩, hb⟩ := h
    simp only [resolveExpr, resolveExpr_closed scope s hs,
      resolveExpr_closed scope e he, resolveExpr_closed_list scope body hb]
  | scope, .block es, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed_list scope es h
  | scope, .match_ scrut arms, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope scrut h.1, resolveExpr_closed_arms scope arms h.2⟩
  | scope, .field_ e name, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .pipe e f, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope e h.1, resolveExpr_closed scope f h.2⟩
  | scope, .typeAsc e τ, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .some_ e, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | _, .none_, _ => rfl
  | scope, .ok_ e, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .err_ e, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .nullCoalesce a b, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope a h.1, resolveExpr_closed scope b h.2⟩
  | scope, .tuple_ es, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed_list scope es h
  | scope, .arrayLit es, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed_list scope es h
  | scope, .arrayIndex a i, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope a h.1, resolveExpr_closed scope i h.2⟩
  | scope, .refCreate e c τ, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .refLoad e, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .refStore r v τ, h => by
    simp [resolveExpr, hasFVar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨resolveExpr_closed scope r h.1, resolveExpr_closed scope v h.2⟩
  | scope, .refFree e, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h
  | scope, .refCast e c, h => by
    simp [resolveExpr, hasFVar] at h ⊢
    exact resolveExpr_closed scope e h

end

end Morph.Frontend.NameResolution
