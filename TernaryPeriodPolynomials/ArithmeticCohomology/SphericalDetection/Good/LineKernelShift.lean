module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineRadicalRealShift_mul (first second : RadicalLattice) (real : ℝ × ℝ) :
    goodLineRadicalRealShift first (goodLineRadicalRealShift second real) =
      goodLineRadicalRealShift (first * second) real := by
  ext <;> simp [goodLineRadicalRealShift, mul_add] <;> ring

theorem goodLineRadicalRealShift_one (real : ℝ × ℝ) :
    goodLineRadicalRealShift 1 real = real := by
  ext <;> simp [goodLineRadicalRealShift]

theorem integral_goodLineRadicalRealShift {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (function : ℝ × ℝ → E) (radical : RadicalLattice) :
    (∫ real : ℝ × ℝ, function (goodLineRadicalRealShift radical real)
      ∂((volume : Measure ℝ).prod volume)) =
      ∫ real : ℝ × ℝ, function real ∂((volume : Measure ℝ).prod volume) :=
  integral_add_right_eq_self function
    (3 * (radical.toAdd.2 : ℝ), 3 * (radical.toAdd.1 : ℝ))

theorem integrable_goodLineRadicalRealShift {E : Type*} [NormedAddCommGroup E]
    (function : ℝ × ℝ → E) (radical : RadicalLattice) :
    Integrable (fun real => function (goodLineRadicalRealShift radical real))
      ((volume : Measure ℝ).prod volume) ↔
    Integrable function ((volume : Measure ℝ).prod volume) := by
  constructor
  · intro integrable
    have shifted := integrable.comp_add_right
      (3 * ((radical⁻¹).toAdd.2 : ℝ), 3 * ((radical⁻¹).toAdd.1 : ℝ))
    change Integrable (fun real => function
      (goodLineRadicalRealShift radical (goodLineRadicalRealShift radical⁻¹ real))) _ at shifted
    simpa only [goodLineRadicalRealShift_mul, mul_inv_cancel, goodLineRadicalRealShift_one] using shifted
  · intro integrable
    exact integrable.comp_add_right
      (3 * (radical.toAdd.2 : ℝ), 3 * (radical.toAdd.1 : ℝ))

theorem integral_goodLineKernel_shift (parameter : ℂ) (radical : RadicalLattice)
    (function : ℝ × ℝ → ℂ) :
    (∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
      function (goodLineRadicalRealShift radical real) ∂((volume : Measure ℝ).prod volume)) =
    ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter
      (goodLineRadicalRealShift radical⁻¹ real) * function real
      ∂((volume : Measure ℝ).prod volume) := by
  have translated := integral_goodLineRadicalRealShift
    (fun real => standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) *
      function real) radical
  simpa only [goodLineRadicalRealShift_mul, inv_mul_cancel, goodLineRadicalRealShift_one] using translated

theorem integral_goodLineKernel_difference (parameter : ℂ) (radical : RadicalLattice)
    (function : ℝ × ℝ → ℂ)
    (original : Integrable (fun real => standardGoodLineRealKernel parameter real * function real)
      ((volume : Measure ℝ).prod volume))
    (translated : Integrable (fun real => standardGoodLineRealKernel parameter real *
      function (goodLineRadicalRealShift radical real)) ((volume : Measure ℝ).prod volume)) :
    (∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
      (function (goodLineRadicalRealShift radical real) - function real)
      ∂((volume : Measure ℝ).prod volume)) =
    ∫ real : ℝ × ℝ, (standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) -
      standardGoodLineRealKernel parameter real) * function real
      ∂((volume : Measure ℝ).prod volume) := by
  have shifted : Integrable (fun real =>
      standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) * function real)
      ((volume : Measure ℝ).prod volume) := by
    apply (integrable_goodLineRadicalRealShift _ radical).mp
    simpa only [goodLineRadicalRealShift_mul, inv_mul_cancel, goodLineRadicalRealShift_one] using translated
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub translated original, integral_sub shifted original, integral_goodLineKernel_shift]

theorem goodLineKernel_difference_endpoint (radical : RadicalLattice) (real : ℝ × ℝ) :
    standardGoodLineRealKernel cohomologicalPoint (goodLineRadicalRealShift radical⁻¹ real) -
      standardGoodLineRealKernel cohomologicalPoint real = 0 := by
  rw [standardGoodLineRealKernel_endpoint, standardGoodLineRealKernel_endpoint, sub_self]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
