module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneLevelCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineIntegralRegion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem standardGoodLineFiniteArgument_three (finite : FiniteAwayThree × FiniteAwayThree) :
    GeneralLinearGroup.map finiteThree (standardGoodLineFiniteArgument finite) =
      weyl⁻¹ * lineUnipotent 0 0 * localGoodLine := by
  have rational : GeneralLinearGroup.map finiteThree (rationalFinite rationalGoodLine) = localGoodLine := by
    have equality := adelicThreeGroup_rational rationalGoodLine
    rw [rationalGoodLine_at_three] at equality
    exact equality
  rw [standardGoodLineFiniteArgument, map_mul, map_mul, map_inv, map_weyl, map_lineUnipotent, rational]
  rw [show finiteThree finite.1.val = 0 from finite.1.property,
    show finiteThree finite.2.val = 0 from finite.2.property]

theorem standardGoodLineFiniteArgument_three_level (finite : FiniteAwayThree × FiniteAwayThree) :
    InLocalThreeLevel (GeneralLinearGroup.map finiteThree (standardGoodLineFiniteArgument finite)) := by
  let compact : LocalThreeIntegralGL :=
    ⟨!![0,1,0;1,0,0;0,0,1], !![0,1,0;1,0,0;0,0,1], by
      funext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
      funext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩
  refine ⟨compact, ?_, ?_⟩
  · funext column
    fin_cases column <;>
      simp [compact, lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three, GeneralLinearGroup.map_apply]
  · apply Units.ext
    rw [standardGoodLineFiniteArgument_three, localStandardMatrix]
    funext row column
    fin_cases row <;> fin_cases column <;> simp [compact, GeneralLinearGroup.map_apply]

theorem finitePlaneLevelCoordinates_nonempty (argument : FiniteGL)
    (three : InLocalThreeLevel (GeneralLinearGroup.map finiteThree argument)) :
    Nonempty (FinitePlaneLevelCoordinates argument) := by
  obtain ⟨parabolic, compact, parabolic_three, factors⟩ := finiteGL_plane_level_factorization argument three
  obtain ⟨first, second, scalar, block, parabolic_factors⟩ := planeParabolic_exists_decomposition parabolic
  have coordinate_values := planeInduction_coordinates_map_eq_one finiteThree first second scalar block
    (by rw [← parabolic_factors]; exact parabolic_three)
  refine ⟨⟨first, second, scalar, block, compact, coordinate_values.1, coordinate_values.2, ?_⟩⟩
  rw [factors, parabolic_factors, mul_assoc, mul_assoc]

def standardGoodLineFiniteCoordinates (finite : FiniteAwayThree × FiniteAwayThree) :
    FinitePlaneLevelCoordinates (standardGoodLineFiniteArgument finite) :=
  Classical.choice (finitePlaneLevelCoordinates_nonempty _ (standardGoodLineFiniteArgument_three_level finite))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
