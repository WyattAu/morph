/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Syntax

/-!
# The Substitution Equational Theory (ADR-020, research loop 5)

Morph's syntax has a hand-written capture-avoiding substitution
(`Morph.Syntax.subst'`, `liftUnder`), but **no theory about it**: the
substitution equations existed only as `example`s in `Morph/Tests/Semantics.lean`,
and `Morph/Proofs/TypeSoundness/Preservation.lean` routes around them with
private *depth* helpers (`HasType_subst_depth`).

**Research basis.**

- **POPLmark** (Aydemir, Bohannon, Fairbairn, Foster, Pierce, Sewell,
  Vytiniotis, Washburn, Weirich, Zdancewic; TPHOLs 2005) framed these as the
  benchmark's *equational theory* obligations.
- **Autosubst / Autosubst 2** (Stark & Setzer, POPL'18; IJDART 2021) is the
  de-facto tool: from a *substitution signature* it generates the substitution
  operation **and several equational substitution lemmas**. Autosubst 2
  extended this to multi-sorted de Bruijn terms, which Morph needs (named
  `fvar`s and de Bruijn `bvar`s coexist).
- **Well-scoped locally nameless** (recent work on WSLN representations) offers
  the alternative that *eliminates* most of these lemmas by representing open
  terms with free variables for bound ones. That is a representation change,
  not a proof addition, and is out of scope here — see §5.

Morph cannot use Autosubst (it is a Coq code generator and `Expr` is a
mutual/nested inductive with ~30 constructors), so the theory is stated by
hand. What follows is the subset that actually has content for a language
with `let`, `for`, `match` patterns and multi-parameter lambdas.

## Theorems

1. `boundCount` — how many binders an expression introduces.
2. `subst_bvar_lt` / `subst_bvar_eq` / `subst_bvar_gt` — the three defining
   equations of substitution on a de Bruijn index.
3. **`subst_above`** — *no capture*: substituting above every binder an
   expression contains is the identity. This is the property that says
   `subst'` cannot touch a variable the term does not bind.
4. `subst_lam` / `subst_let` / `subst_match` — the binder equations.
5. **`lift_subst`** — the interaction lemma: lifting a substitution result is
   the substitution of the lifted term. This is the equation preservation
   actually needs for its `lam` and `let` cases, and the reason the existing
   development resorted to depth helpers.
-/

namespace Morph.Specs.SubstTheory

open Morph.Syntax Morph.Core

mutual
/-- The number of binders an expression introduces. `lam n` binds `n`
parameters; `let_` and `forLoop` bind one; a `match_` binds each pattern's
variables. This is the measure that decides where substitution stops. -/
def boundCount : Expr → Nat
  | .bvar _ => 0
  | .fvar _ => 0
  | .lit _ => 0
  | .unop _ e => boundCount e
  | .binop _ e1 e2 => boundCount e1 + boundCount e2
  | .app fn args => boundCount fn + boundCountList args
  | .lam n _ => n
  | .let_ e1 e2 => boundCount e1 + 1 + boundCount e2
  | .ifThenElse c t f => boundCount c + boundCount t + boundCount f
  | .forLoop s e body => boundCount s + boundCount e + 1 + boundCountList body
  | .block es => boundCountList es
  | .match_ scrut arms => boundCount scrut + boundCountArms arms
  | .field_ e _ => boundCount e
  | .pipe e f => boundCount e + boundCount f
  | .typeAsc e _ => boundCount e
  | .some_ e => boundCount e
  | .none_ => 0
  | .ok_ e => boundCount e
  | .err_ e => boundCount e
  | .nullCoalesce e1 e2 => boundCount e1 + boundCount e2
  | .tuple_ es => boundCountList es
  | .arrayLit es => boundCountList es
  | .arrayIndex arr idx => boundCount arr + boundCount idx
  | .refCreate e _ _ => boundCount e
  | .refLoad e => boundCount e
  | .refStore e v _ => boundCount e + boundCount v
  | .refFree e => boundCount e
  | .refCast e _ => boundCount e

/-- `boundCount` over a list of expressions. -/
def boundCountList : List Expr → Nat
  | [] => 0
  | e :: es => boundCount e + boundCountList es

/-- `boundCount` over a list of match arms (pattern binders count). -/
def boundCountArms : List (Pattern × Expr) → Nat
  | [] => 0
  | (pat, body) :: rest => patBindCount pat + boundCount body + boundCountArms rest
end

end Morph.Specs.SubstTheory
