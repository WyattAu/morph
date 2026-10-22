import Morph.Specs.UnitGroupTheory.Lemmas

namespace Morph.Specs.UnitGroupTheory

/-- The two stubs, now proved. -/
example : spec_exchange_rate_invariant := fun u => div_self_dimensionless u
example : spec_unit_names_unique := base_unit_vectors_distinct

/-- The algebra. -/
example (v1 v2 : UnitVector) (h : v1.exponents.length = v2.exponents.length) :
    addUnitVectors v1 v2 = addUnitVectors v2 v1 :=
  addUnitVectors_comm v1 v2 h

/-- A dimensionless quantity, computed. -/
example : evaluateUnitExpression (.div (.base .currency) (.base .currency))
    = identityVector 4 := rfl

end Morph.Specs.UnitGroupTheory
