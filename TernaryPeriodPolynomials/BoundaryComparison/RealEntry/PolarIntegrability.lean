module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.IntegrandPolar
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Integrability
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-! Integrability of the polar-rewritten integrand on `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`,
needed to apply Fubini (`MeasureTheory.setIntegral_prod`) in clause (iii) of
`real_constant_term_entry` (Appendix C.5). -/


open MeasureTheory Set

namespace TernaryPeriodPolynomials.Argument

/-- Pointwise norm bound for the polar-rewritten integrand, purely in terms of `ρ`. -/
theorem entryIntegrand_polar_norm_le (n : ℕ) (ρ θ : ℝ) :
    ‖entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ)‖ ≤ (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ 3 := by
  have h := entryIntegrand_norm_le n (ρ * Real.sin θ) (ρ * Real.cos θ)
  rwa [entryRadius_polar ρ θ (Real.sqrt (1 + ρ ^ 2))
    (Real.sq_sqrt (by positivity)) (Real.sqrt_pos.mpr (by positivity))] at h

/-- `ρ (√(1+ρ²))⁻¹³ ≤ 2√2 (1+ρ)^{-2}`, combining `entryRadius_inv_cube_le` (second coordinate
`0`) with `ρ(1+ρ)^{-3} ≤ (1+ρ)^{-2}`. -/
theorem radial_scaled_dominant_bound (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ 3 ≤ 2 * Real.sqrt 2 * (1 + ρ) ^ (-(2 : ℝ)) := by
  have hradius : entryRadius (ρ, 0) = Real.sqrt (1 + ρ ^ 2) := by
    unfold entryRadius; norm_num
  have hmax : max |ρ| |(0 : ℝ)| = ρ := by
    rw [abs_of_nonneg hρ, abs_zero, max_eq_left hρ]
  have hstep1 : (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ 3 ≤ 2 * Real.sqrt 2 * (1 + ρ) ^ (-(3 : ℝ)) := by
    have h := entryRadius_inv_cube_le ρ 0
    rwa [hradius, hmax] at h
  have h1ρ : (0 : ℝ) < 1 + ρ := by linarith
  have hpow_pos : (0 : ℝ) < (1 + ρ) ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos h1ρ _
  have hstep2 : ρ * (1 + ρ) ^ (-(3 : ℝ)) ≤ (1 + ρ) ^ (-(2 : ℝ)) := by
    have hexp : (-(2 : ℝ)) = (-(3 : ℝ)) + 1 := by norm_num
    rw [hexp, Real.rpow_add h1ρ, Real.rpow_one]
    calc ρ * (1 + ρ) ^ (-(3 : ℝ)) ≤ (1 + ρ) * (1 + ρ) ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) hpow_pos.le
      _ = (1 + ρ) ^ (-(3 : ℝ)) * (1 + ρ) := mul_comm _ _
  calc ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ 3
      ≤ ρ * (2 * Real.sqrt 2 * (1 + ρ) ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep1 hρ
    _ = 2 * Real.sqrt 2 * (ρ * (1 + ρ) ^ (-(3 : ℝ))) := by ring
    _ ≤ 2 * Real.sqrt 2 * (1 + ρ) ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)

/-- The scaled polar integrand `ρ • entryIntegrand n (ρ sinθ, ρ cosθ)` is dominated, in norm, by
`2√2(1+‖ρ‖)^{-2}` (phrased with `‖ρ‖` to match `integrable_one_add_norm`'s shape). -/
theorem scaled_entryIntegrand_polar_norm_le (n : ℕ) (ρ θ : ℝ) (hρ : 0 < ρ) :
    ‖ρ • entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ)‖ ≤
      2 * Real.sqrt 2 * (1 + ‖ρ‖) ^ (-(2 : ℝ)) := by
  have hρ' : ‖ρ‖ = ρ := by rw [Real.norm_eq_abs, abs_of_pos hρ]
  rw [norm_smul, hρ']
  calc ρ * ‖entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ)‖
      ≤ ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_left (entryIntegrand_polar_norm_le n ρ θ) hρ.le
    _ ≤ 2 * Real.sqrt 2 * (1 + ρ) ^ (-(2 : ℝ)) := radial_scaled_dominant_bound ρ hρ.le

/-- `IntegrableOn (fun ρ => 2√2(1+‖ρ‖)^{-2}) (Ioi 0) volume`, via `integrable_one_add_norm`. -/
theorem radial_dominant_integrableOn :
    IntegrableOn (fun ρ : ℝ => 2 * Real.sqrt 2 * (1 + ‖ρ‖) ^ (-(2 : ℝ))) (Set.Ioi 0) volume := by
  have hfr : (Module.finrank ℝ ℝ : ℝ) < 2 := by rw [Module.finrank_self]; norm_num
  exact ((integrable_one_add_norm hfr).const_mul (2 * Real.sqrt 2)).integrableOn

/-- `Ioo (-π) π` has finite volume. -/
theorem isFiniteMeasure_restrict_Ioo_pi :
    IsFiniteMeasure (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  exact ENNReal.ofReal_lt_top

/-- Lift `radial_dominant_integrableOn` to the product domain `Ioi 0 ×ˢ Ioo (-π) π`, tensoring
with the finite measure of `Ioo (-π) π`. -/
theorem radial_dominant_integrableOn_prod :
    IntegrableOn (fun p : ℝ × ℝ => 2 * Real.sqrt 2 * (1 + ‖p.1‖) ^ (-(2 : ℝ)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) volume := by
  have := isFiniteMeasure_restrict_Ioo_pi
  have h := radial_dominant_integrableOn.comp_fst (volume.restrict (Set.Ioo (-Real.pi) Real.pi))
  rwa [Measure.prod_restrict] at h

/-- The scaled polar-rewritten integrand is integrable on `Ioi 0 ×ˢ Ioo (-π) π`. -/
theorem entryIntegrand_polar_integrableOn (n : ℕ) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 • entryIntegrand n (p.1 * Real.sin p.2, p.1 * Real.cos p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) volume := by
  refine Integrable.mono' radial_dominant_integrableOn_prod ?_ ?_
  · exact (continuous_fst.smul ((entryIntegrand_continuous n).comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 * Real.sin p.2, p.1 * Real.cos p.2)))))
      |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem
        (by measurability : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi))]
      with p hp
    exact scaled_entryIntegrand_polar_norm_le n p.1 p.2 hp.1

end TernaryPeriodPolynomials.Argument
