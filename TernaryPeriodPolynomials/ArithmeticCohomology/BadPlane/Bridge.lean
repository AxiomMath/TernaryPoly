module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.Clauses
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.Tables

@[expose] public section


/-!
# The two models of the plane radical `N_P` and of the Levi section agree

Formalized by Claude Sonnet 5.5.

`BadPlaneTables` works with the lattice model of the original library (`planeHom : ℤ² → GL₃(ℤ)`, `planeElement A u`), `BadPlaneClauses` with the `K†`-level model of `SphericalDetection`
(`identityPlaneRadicalInclusion`, `identityPlaneLeviSection`, with values in `GL₃(ℚ)`).  This file shows that they are the same matrices:
`identityPlaneRadicalInclusion g = planeHom g` and `identityPlaneLeviSection A = planeElement A 0` in `GL₃(ℚ)`.
-/

open Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPoly.RadicalFirstCohomologyLattice TernaryPoly.RelativeStabilizerParameters
open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.BadPlane

theorem radicalInclusion_eq_planeHom (g : Multiplicative (ℤ × ℤ)) :
    ((identityPlaneRadicalInclusion g).val : RationalGL3) =
      GeneralLinearGroup.map (Int.castRingHom ℚ) (planeHom g) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [identityPlaneRadicalInclusion, upperRadicalLattice, planeUnipotent, planeHom,
      TernaryPoly.RelativeStabilizerParameters.planeElement_val, TernaryPoly.RelativeStabilizerMatrices.planeMatrix,
      GeneralLinearGroup.map_apply]


theorem leviSection_eq_planeElement (A : GL (Fin 2) ℤ) :
    ((identityPlaneLeviSection A).val : RationalGL3) =
      GeneralLinearGroup.map (Int.castRingHom ℚ) (planeElement A 0) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [identityPlaneLeviSection, arithmeticLeviHom, arithmeticLevi, planeLevi, planeBlock,
      TernaryPoly.RelativeStabilizerParameters.planeElement_val,
      TernaryPoly.RelativeStabilizerMatrices.planeMatrix, GeneralLinearGroup.map_apply]

end TernaryPeriodPolynomials.Argument.Identities.BadPlane
