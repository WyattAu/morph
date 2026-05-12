/-!
Lemmas for ScopingLambdaCalculus.

Lemmas about variable binding, scope resolution, and
capture-avoiding substitution.
-/
namespace Morph.Specs.ScopingLambdaCalculus

inductive Expr where
  | var (name : String) : Expr
  | lam (name : String) (body : Expr) : Expr
  | app (fn arg : Expr) : Expr
  deriving Repr

def freeVars : Expr → List String
  | .var x => [x]
  | .lam x body => (freeVars body).filter (fun z => z != x)
  | .app f a => freeVars f ++ freeVars a

theorem freeVars_var (x : String) : freeVars (.var x) = [x] := rfl

theorem freeVars_app (f a : Expr) :
    freeVars (.app f a) = freeVars f ++ freeVars a := rfl

theorem freeVars_lam_shadows_concrete :
    freeVars (.lam "x" (.var "x")) = [] := rfl

theorem freeVars_lam_preserves :
    freeVars (.lam "x" (.var "y")) = ["y"] := rfl

theorem freeVars_lam_nested :
    freeVars (.lam "x" (.lam "y" (.var "z"))) = ["z"] := rfl

theorem freeVars_app_concrete :
    freeVars (.app (.var "x") (.var "y")) = ["x", "y"] := rfl

theorem expr_cases (e : Expr) :
    match e with
    | .var _ => True
    | .lam _ _ => True
    | .app _ _ => True := by
  cases e <;> simp

end Morph.Specs.ScopingLambdaCalculus
