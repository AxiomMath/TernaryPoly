module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneFirstProjection_contDiffAt {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (input : P → RealGL3) (center : P)
    (regular : ContDiffAt ℝ ⊤ (fun point => (input point).val) center)
    (pivot : (input center).val 2 0 ≠ 0) :
    ContDiffAt ℝ ⊤ (fun point => (realPlaneMatrix (realPlaneFirstProjection (input point))).val) center := by
  apply realPlaneOpenProjection_contDiffAt
    (fun point => input point * GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine) center
  · apply contDiffAt_pi.mpr
    intro row
    apply contDiffAt_pi.mpr
    intro column
    change ContDiffAt ℝ ⊤ (fun point => ∑ middle, (input point).val row middle *
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine).val middle column) center
    exact ContDiffAt.sum (fun middle _ =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp regular row) middle).mul contDiffAt_const)
  · rwa [realPlaneFirstProjection_pivot]

theorem affinePlaneZero_measure (first second constant : ℝ)
    (nonzero : first ≠ 0 ∨ second ≠ 0 ∨ constant ≠ 0) :
    ((volume : Measure ℝ).prod volume) {real : ℝ × ℝ | first * real.1 + second * real.2 + constant = 0} = 0 := by
  have continuous : Continuous (fun real : ℝ × ℝ => first * real.1 + second * real.2 + constant) := by fun_prop
  have measurable : MeasurableSet {real : ℝ × ℝ | first * real.1 + second * real.2 + constant = 0} :=
    (isClosed_eq continuous continuous_const).measurableSet
  by_cases second_ne : second ≠ 0
  · apply Measure.measure_prod_null_of_ae_null measurable
    filter_upwards [] with sample
    have fiber : Prod.mk sample ⁻¹' {real : ℝ × ℝ | first * real.1 + second * real.2 + constant = 0} =
        {-(first * sample + constant) / second} := by
      ext value
      change first * sample + second * value + constant = 0 ↔ value = -(first * sample + constant) / second
      rw [eq_div_iff second_ne]
      constructor <;> intro equality <;> linarith
    rw [fiber]
    exact measure_singleton _
  · have second_zero : second = 0 := not_ne_iff.mp second_ne
    by_cases first_ne : first ≠ 0
    · have set_eq : {real : ℝ × ℝ | first * real.1 + second * real.2 + constant = 0} =
          {-(constant / first)} ×ˢ (Set.univ : Set ℝ) := by
        ext real
        simp only [second_zero, zero_mul, add_zero, Set.mem_ofPred_eq, Set.mem_prod,
          Set.mem_singleton_iff, Set.mem_univ, and_true]
        rw [← neg_div, eq_div_iff first_ne]
        constructor <;> intro equality <;> linarith
      rw [set_eq]
      simp
    · have first_zero : first = 0 := not_ne_iff.mp first_ne
      have constant_ne : constant ≠ 0 := nonzero.resolve_left first_ne |>.resolve_left second_ne
      simp [first_zero, second_zero, constant_ne]

theorem goodLineFirstProjection_pivot_ae (vertex : RealGL3) :
    ∀ᵐ real : ℝ × ℝ ∂((volume : Measure ℝ).prod volume),
      (standardGoodLineRealArgument real * vertex).val 2 0 ≠ 0 := by
  have nonzero : vertex.val 1 0 ≠ 0 ∨ vertex.val 0 0 ≠ 0 ∨ vertex.val 2 0 ≠ 0 := by
    by_contra failure
    push Not at failure
    have determinant : vertex.val.det = 0 := by
      rw [Matrix.det_fin_three, failure.1, failure.2.1, failure.2.2]
      ring
    exact (GeneralLinearGroup.det vertex).ne_zero determinant
  have equality (real : ℝ × ℝ) : (standardGoodLineRealArgument real * vertex).val 2 0 =
      vertex.val 1 0 * real.1 + vertex.val 0 0 * real.2 + vertex.val 2 0 := by
    rw [GeneralLinearGroup.coe_mul, standardGoodLineRealArgument_val, Matrix.mul_apply, Fin.sum_univ_three]
    change real.2 * vertex.val 0 0 + real.1 * vertex.val 1 0 + 1 * vertex.val 2 0 = _
    ring
  simp only [equality]
  rw [ae_iff]
  simpa only [not_not] using affinePlaneZero_measure (vertex.val 1 0) (vertex.val 0 0) (vertex.val 2 0) nonzero

theorem goodLineFirstProjection_vertices_ae {length : ℕ} (vertices : Fin length → RealGL3) :
    ∀ᵐ real : ℝ × ℝ ∂((volume : Measure ℝ).prod volume),
      ∀ position, (standardGoodLineRealArgument real * vertices position).val 2 0 ≠ 0 := by
  rw [ae_all_iff]
  exact fun position => goodLineFirstProjection_pivot_ae (vertices position)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
