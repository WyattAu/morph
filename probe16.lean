import Morph.Specs.TypeUnification.Spec
namespace Morph.Specs.TypeUnification

theorem apply_id2 : ∀ t, apply Subst.id t = t := by
  intro t
  induction t with
  | v _ => rfl
  | c _ => rfl
  | arrow a b ihp ihb =>
      show UTerm.arrow (apply Subst.id a) (apply Subst.id b) = UTerm.arrow a b
      rw [ihp, ihb]

end Morph.Specs.TypeUnification
