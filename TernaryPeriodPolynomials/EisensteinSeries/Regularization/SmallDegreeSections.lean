module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.RowReduction
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.VectorParameters

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedCuspVector_small_degree_integral_zero
    {degree : ℕ} (small : degree < 3) {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL)
    (finite_integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    normalizedCuspVector induced parameter matrix = 0 := by
  obtain ⟨integralMatrix, represents⟩ := finite_integral
  obtain ⟨binary, row_zero⟩ := integral_plane_row_reduction integralMatrix
  let translated := atFinite (planeLevi (SpecialLinearGroup.mapGL FiniteAdeles binary) 1) * matrix
  have translated_represents : GeneralLinearGroup.map integralEmbedding
      (planeLevi (SpecialLinearGroup.mapGL IntegralAdeles binary) 1 * integralMatrix) = finiteGroup translated := by
    simp only [translated, map_mul, map_planeLevi, map_one, binaryIntegral_mapGL_map,
      represents, finiteGroup_atFinite]
  have translated_zero : normalizedCuspVector induced parameter translated = 0 :=
    cohomological_small_degree_rowLevel_zero inducingData.cohomological small
      ⟨normalizedCuspVector induced parameter translated,
        normalizedCuspVector_binaryRowLevel_fixed induced parameter translated _ translated_represents row_zero⟩
  have norm_one : normPower (GeneralLinearGroup.det (atFinite (SpecialLinearGroup.mapGL FiniteAdeles binary)))
      (inductionExponent .plane parameter) = 1 := by
    rw [← binaryIntegral_mapGL_map integralEmbedding binary]
    exact binaryIntegral_det_normPower _ _
  change normalizedCuspVector induced parameter
    (atFinite (planeLevi (SpecialLinearGroup.mapGL FiniteAdeles binary) 1) * matrix) = 0 at translated_zero
  rw [atFinite_planeLevi, normalizedCuspVector_binary, norm_one, one_smul] at translated_zero
  by_contra nonzero
  exact cuspSmoothAction_ne_zero inducingData.cusp _ _ nonzero translated_zero

theorem normalizedCuspVector_small_degree_zero
    {degree : ℕ} (small : degree < 3) {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) : normalizedCuspVector induced parameter matrix = 0 := by
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, compact⟩ :=
    adelic_plane_levi_decomposition matrix
  apply Subtype.ext
  apply norm_eq_zero.mp
  rw [decomposition, mul_assoc, normalizedCuspVector_unipotent, planeLevi_rankOne_binary binary scalar,
    mul_assoc, normalizedCuspVector_rankOne_norm, normalizedCuspVector_binary_norm,
    normalizedCuspVector_small_degree_integral_zero small induced parameter compactMatrix compact.2]
  simp

theorem unitaryNormalize_small_degree_zero
    {degree : ℕ} (small : degree < 3) {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter)) :
    unitaryNormalize degree family = 0 := by
  funext parameter matrix
  rw [← normalizedCuspVector_at_one induced parameter matrix,
    normalizedCuspVector_small_degree_zero small induced parameter matrix, map_zero]
  rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
