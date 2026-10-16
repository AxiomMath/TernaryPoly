module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearLipschitzKernels
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem realSpecialTent_detects_nonnegative_at_one {function : RealSL3 → ℝ}
    (continuous : Continuous function) (nonnegative : 0 ≤ function 1)
    (zero : ∀ radius : ℝ, (∫ matrix, (realSpecialTent radius matrix).re * function matrix ∂realSpecialLinearHaar) = 0) :
    function 1 = 0 := by
  by_contra nonzero
  have positive : 0 < function 1 := lt_of_le_of_ne nonnegative (Ne.symm nonzero)
  have positive_near : {matrix | 0 < function matrix} ∈ nhds (1 : RealSL3) :=
    continuous.continuousAt.eventually (lt_mem_nhds positive)
  have inducing : Topology.IsInducing (fun matrix : RealSL3 => matrix.val) :=
    SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing
  rw [inducing.nhds_eq_comap] at positive_near
  obtain ⟨ambient, ambient_neighborhood, ambient_positive⟩ := Filter.mem_comap.mp positive_near
  obtain ⟨radius, radius_positive, neighborhood⟩ := Metric.mem_nhds_iff.mp ambient_neighborhood
  have tent_continuous : Continuous (fun matrix => (realSpecialTent radius matrix).re * function matrix) :=
    (Complex.continuous_re.comp (realSpecialTent_continuous radius)).mul continuous
  have support : HasCompactSupport (fun matrix => (realSpecialTent radius matrix).re * function matrix) :=
    ((realSpecialTent_compactSupport radius).comp_left (by simp : Complex.re 0 = 0)).mul_right
  have nonnegative_product : 0 ≤ (fun matrix => (realSpecialTent radius matrix).re * function matrix) := by
    intro matrix
    by_cases inside : ‖matrix.val - 1‖ < radius
    · apply mul_nonneg
      · change 0 ≤ max 0 (radius - ‖matrix.val - 1‖)
        exact le_max_left _ _
      · exact le_of_lt (ambient_positive (neighborhood inside))
    · have vanishes : realSpecialTent radius matrix = 0 := by
        simp only [realSpecialTent, max_eq_left (sub_nonpos.mpr (le_of_not_gt inside)), Complex.ofReal_zero]
      simp only [vanishes, Complex.zero_re, zero_mul, Pi.zero_apply, le_refl]
  have at_one : (realSpecialTent radius (1 : RealSL3)).re * function 1 ≠ 0 := by
    simpa [realSpecialTent, max_eq_right radius_positive.le] using ne_of_gt (mul_pos radius_positive positive)
  have integral_positive := tent_continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := realSpecialLinearHaar) support nonnegative_product at_one
  rw [zero] at integral_positive
  exact (lt_irrefl 0) integral_positive

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
