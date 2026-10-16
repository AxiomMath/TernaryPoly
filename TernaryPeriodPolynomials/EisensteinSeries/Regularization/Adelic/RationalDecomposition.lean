module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.RationalDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem realGroup_rational (matrix : RationalGL3) :
    realGroup (rationalGroup matrix) = GeneralLinearGroup.map (algebraMap ℚ ℝ) matrix := by
  apply Units.ext
  rfl

theorem finiteGroup_rational (matrix : RationalGL3) :
    finiteGroup (rationalGroup matrix) =
      GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix := by
  apply Units.ext
  rfl

theorem adelic_rational_real_integral (matrix : AdelicGL) :
    ∃ rational : RationalGL3, ∃ realMatrix : RealGL3, ∃ integralMatrix : GL3 IntegralAdeles,
      matrix = rationalGroup rational * atInfinity realMatrix *
        atFinite (GeneralLinearGroup.map integralEmbedding integralMatrix) := by
  obtain ⟨rational, integralMatrix, decomposition⟩ :=
    finite_rational_integral_decomposition (finiteGroup matrix)
  refine ⟨rational, (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)⁻¹ * realGroup matrix,
    integralMatrix, ?_⟩
  apply adelicGroup_eq_of_components
  · rw [map_mul, map_mul, realGroup_rational, realGroup_atInfinity, realGroup_atFinite,
      mul_one, mul_inv_cancel_left]
  · rw [map_mul, map_mul, finiteGroup_rational, finiteGroup_atInfinity, finiteGroup_atFinite,
      mul_one]
    exact decomposition

theorem adelic_rational_translate_integral (matrix : AdelicGL) :
    ∃ rational : RationalGL3,
      finiteGroup (rationalGroup rational * matrix) ∈
        Set.range (GeneralLinearGroup.map integralEmbedding) := by
  obtain ⟨rational, integralMatrix, decomposition⟩ :=
    finite_rational_integral_decomposition (finiteGroup matrix)
  refine ⟨rational⁻¹, integralMatrix, ?_⟩
  rw [map_mul, finiteGroup_rational, map_inv, decomposition, inv_mul_cancel_left]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
