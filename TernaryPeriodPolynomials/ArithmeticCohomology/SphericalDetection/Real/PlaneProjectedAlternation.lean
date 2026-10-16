module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.CentralIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneRadicalCoefficients
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneRestriction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneInversionLevi : RealPlaneGroup :=
  identityPlaneRealGroup (identityPlaneLeviSection (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)))

theorem realPlaneInversionLevi_conjugates (radical : RadicalLattice) :
    realPlaneInversionLevi⁻¹ * realPlaneLatticeRadical radical * realPlaneInversionLevi =
      realPlaneLatticeRadical radical⁻¹ := by
  have equality := congrArg identityPlaneRealGroup (identityPlaneLevi_neg_one_conjugates radical)
  simp only [map_mul, map_inv, identityPlaneRealGroup_radical] at equality
  rw [map_inv]
  exact equality

def realPlaneLevelBinaryValue (degree : ℕ) (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL) :
    realPlaneLevelCuspidalRep degree cusp trivialCharacter →ₗ[ℂ] Binary.HomogeneousPoly degree where
  toFun values := binaryHomogeneousRestrict degree (values.val.val argument)
  map_add' _ _ := (binaryHomogeneousRestrict degree).map_add _ _
  map_smul' scalar _ := (binaryHomogeneousRestrict degree).map_smul scalar _

theorem realPlaneLevelBinaryValue_radical (degree : ℕ) (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (radical : RadicalLattice) (values : realPlaneLevelCuspidalRep degree cusp trivialCharacter) :
    realPlaneLevelBinaryValue degree cusp argument
      ((realPlaneLevelCuspidalRep degree cusp trivialCharacter).ρ (realPlaneLatticeRadical radical) values) =
        realPlaneLevelBinaryValue degree cusp argument values := by
  change binaryHomogeneousRestrict degree
    (((realPlaneCuspidalRep degree cusp trivialCharacter).ρ (realPlaneLatticeRadical radical) values.val).val argument) = _
  rw [realPlaneCuspidalRep_latticeRadical, binaryHomogeneousRestrict_upperLattice]
  rfl

theorem realPlaneLevelBinaryValue_inversion (degree : ℕ) (odd : Odd degree) (cusp : CuspidalRepresentation)
    (argument : BinaryAdelicGL) (values : realPlaneLevelCuspidalRep degree cusp trivialCharacter) :
    realPlaneLevelBinaryValue degree cusp argument
      ((realPlaneLevelCuspidalRep degree cusp trivialCharacter).ρ realPlaneInversionLevi values) =
        -realPlaneLevelBinaryValue degree cusp argument values := by
  change binaryHomogeneousRestrict degree
    (((realPlaneCuspidalRep degree cusp trivialCharacter).ρ realPlaneInversionLevi values.val).val argument) =
      -binaryHomogeneousRestrict degree (values.val.val argument)
  rw [realPlaneInversionLevi, realPlaneCuspidalRep_apply, identityPlaneRealGroup_right,
    identityPlaneLeviProjection_section, normPower_binaryIntegralReal, one_smul,
    cuspidalTensorFiniteLevel_centralIntegralReal cusp values.val values.property (-1) argument,
    identityPlaneRealGroup_matrix]
  exact binaryHomogeneousRestrict_scalar_neg_one degree odd (values.val.val argument)

theorem realPlaneLevelTwoCocycle_projected_alternation_zero (degree : ℕ) (odd : Odd degree)
    (cusp : CuspidalRepresentation) (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp trivialCharacter))
    (first second : RadicalLattice) (argument : BinaryAdelicGL) :
    realPlaneLevelBinaryValue degree cusp argument
      (cycle (realPlaneLatticeRadical first, realPlaneLatticeRadical second) -
        cycle (realPlaneLatticeRadical second, realPlaneLatticeRadical first)) = 0 := by
  exact twoCocycle_projected_alternation_zero realPlaneLatticeRadical (realPlaneLevelCuspidalRep degree cusp trivialCharacter)
    (realPlaneLevelBinaryValue degree cusp argument) (realPlaneLevelBinaryValue_radical degree cusp argument)
    realPlaneInversionLevi realPlaneInversionLevi_conjugates (realPlaneLevelBinaryValue_inversion degree odd cusp argument)
    cycle first second

end TernaryPeriodPolynomials.SphericalDetection.Helpers
