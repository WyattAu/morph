/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Syntax

namespace Morph.Proofs.TypeSoundness

mutual
def listExprDepth : List Morph.Syntax.Expr → Nat
  | [] => 0
  | e :: rest => Nat.max (exprDepth e) (listExprDepth rest)

def exprDepth : Morph.Syntax.Expr → Nat
  | .bvar _ => 0
  | .fvar _ => 0
  | .lit _ => 0
  | .unop _ e => exprDepth e + 1
  | .binop _ e1 e2 => Nat.max (exprDepth e1) (exprDepth e2) + 1
  | .app fn args => Nat.max (exprDepth fn) (listExprDepth args) + 1
  | .lam _ body => exprDepth body + 1
  | .let_ e1 e2 => Nat.max (exprDepth e1) (exprDepth e2) + 1
  | .ifThenElse c t f => Nat.max (exprDepth c) (Nat.max (exprDepth t) (exprDepth f)) + 1
  | .forLoop s e body => Nat.max (exprDepth s) (Nat.max (exprDepth e) (listExprDepth body)) + 1
  | .block exprs => listExprDepth exprs + 1
  | .match_ scrut _ => exprDepth scrut + 1
  | .field_ e _ => exprDepth e + 1
  | .pipe e f => Nat.max (exprDepth e) (exprDepth f) + 1
  | .typeAsc e _ => exprDepth e + 1
  | .some_ e => exprDepth e + 1
  | .none_ => 0
  | .ok_ e => exprDepth e + 1
  | .err_ e => exprDepth e + 1
  | .nullCoalesce e1 e2 => Nat.max (exprDepth e1) (exprDepth e2) + 1
  | .tuple_ elems => listExprDepth elems + 1
  | .arrayLit elems => listExprDepth elems + 1
  | .arrayIndex arr idx => Nat.max (exprDepth arr) (exprDepth idx) + 1
  | .refCreate e _ _ => exprDepth e + 1
  | .refLoad e => exprDepth e + 1
  | .refStore e v _ => Nat.max (exprDepth e) (exprDepth v) + 1
  | .refFree e => exprDepth e + 1
  | .refCast e _ => exprDepth e + 1
end

end Morph.Proofs.TypeSoundness
