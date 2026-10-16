module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneGroupCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.RealPlane

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The retained cusp-valued parabolic cocycle evaluates to the literal arithmetic source cocycle. -/
theorem sourcePlaneGroupCocycle_arithmetic {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (cycle : MaximalCycles degree data.chi .plane)
    (evaluates : Evaluates data .plane source cycle)
    (first second : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    (sourcePlaneGroupCocycle data source cocycle (identityPlaneRealGroup first, identityPlaneRealGroup second)).val 1 =
      ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent degree data.chi)
        (evaluateFlagCycle data.chi .plane (QuotientGroup.mk (1 : RationalGL3)) cycle) (first, second) := by
  rw [sourcePlaneGroupCocycle_apply, map_one, normPower_one, one_smul,
    show planeLevi (1 : BinaryAdelicGL) 1 = 1 from (planeLeviHom Adeles).map_one,
    identityPlaneRealGroup_matrix, identityPlaneRealGroup_matrix, ambientCocycleToGroup_apply]
  change source ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) first.val,
    GeneralLinearGroup.map (algebraMap ℚ ℝ) first.val * GeneralLinearGroup.map (algebraMap ℚ ℝ) second.val] 1 =
      cycle.val.val ![1, first.val, first.val * second.val] (QuotientGroup.mk 1)
  rw [evaluates]
  have tuple : (fun index : Fin 3 => GeneralLinearGroup.map (algebraMap ℚ ℝ) (![1, first.val, first.val * second.val] index)) =
      ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) first.val,
        GeneralLinearGroup.map (algebraMap ℚ ℝ) first.val * GeneralLinearGroup.map (algebraMap ℚ ℝ) second.val] := by
    funext index
    fin_cases index <;> simp
  rw [tuple, inv_one, map_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
