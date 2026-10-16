module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.HighDegree
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Continuous

@[expose] public section

/-! A finite-dimensional compactness step for strictly positive Hodge energy. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

theorem finite_inner_coercivity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hp : ∀ a : E, a ≠ 0 → 0 < inner ℝ (H a) a) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : E, c * inner ℝ a a ≤ inner ℝ (H a) a := by
  by_cases ht : ∀ a : E, a = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro a
    simp [ht a]
  push Not at ht
  obtain ⟨a₀, ha₀⟩ := ht
  have hnorm (a : E) (ha : a ≠ 0) : ‖‖a‖⁻¹ • a‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg a),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]
  have hc : Continuous (fun a : E => inner ℝ (H a) a) :=
    H.continuous_of_finiteDimensional.inner continuous_id
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (show (Metric.sphere (0 : E) 1).Nonempty from
      ⟨‖a₀‖⁻¹ • a₀, by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm a₀ ha₀⟩)
    hc.continuousOn
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  refine ⟨inner ℝ (H b) b, hp b hb0, ?_⟩
  intro a
  by_cases ha : a = 0
  · simp [ha]
  have hu := hmin (show ‖a‖⁻¹ • a ∈ Metric.sphere (0 : E) 1 by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm a ha)
  change inner ℝ (H b) b ≤ inner ℝ (H (‖a‖⁻¹ • a)) (‖a‖⁻¹ • a) at hu
  have hn := norm_pos_iff.mpr ha
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hu
  rw [real_inner_self_eq_norm_sq]
  have hm := mul_le_mul_of_nonneg_left hu (sq_nonneg ‖a‖)
  field_simp at hm ⊢
  nlinarith

end TernaryPoly.SL3PolynomialCoercivity
