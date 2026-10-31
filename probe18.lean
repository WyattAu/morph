import Morph.Specs.ExecutionModel.Spec
namespace Morph.Specs.ExecutionModel
open Morph.Semantics Morph.Store

example (σ σ₁ σ₂ : Morph.Store)
    (op : Morph.Core.Operator) (n1 n2 : Int) (r₁ r₂ : Morph.Syntax.Expr)
    (ha : isArithOp op)
    (h₁ : Step σ (Morph.Syntax.Expr.binop op
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n1))
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n2))) σ₁ r₁)
    (h₂ : Step σ (Morph.Syntax.Expr.binop op
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n1))
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n2))) σ₂ r₂) :
    σ₁ = σ₂ ∧ r₁ = r₂ := by
  cases h₁ <;> cases h₂
  case binop_arith.binop_arith =>
    simp_all

end Morph.Specs.ExecutionModel
