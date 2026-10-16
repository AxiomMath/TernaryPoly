module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem planeLevi_binary_mul {R : Type*} [CommRing R]
    (first second : GeneralLinearGroup (Fin 2) R) :
    planeLevi (first * second) 1 = planeLevi first 1 * planeLevi second 1 := by
  change (planeLeviHom R) (first * second, 1) =
    (planeLeviHom R) (first, 1) * (planeLeviHom R) (second, 1)
  simpa only [Prod.mk_mul_mk, one_mul] using (planeLeviHom R).map_mul (first, 1) (second, 1)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
