module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Average

@[expose] public section


/-!
# Change of variables for the flat measure

The flat Lebesgue measure on the upper half plane is moved by `z ↦ γ z` with the Jacobian
`‖mobDeriv γ z‖²` (`lintegral_flat_mob`, `integral_flat_mob`).  This is the conformal invariance of
the `L²` norm of `1`-forms.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)

/-- The flat Jacobian of the Möbius map. -/
def jac (γ : SL(2, ℤ)) (z : ℂ) : ℝ := ‖mobDeriv γ z‖ ^ 2

theorem measurable_jac (γ : SL(2, ℤ)) : Measurable (jac γ) := by
  unfold jac mobDeriv jfun
  fun_prop

theorem jac_nonneg (γ : SL(2, ℤ)) (z : ℂ) : 0 ≤ jac γ z := by unfold jac; positivity

theorem hmeas_eq : hmeas = (volume.restrict U).withDensity (fun z => ENNReal.ofReal (1 / z.im ^ 2)) := by
  ext s hs
  rw [hmeas_apply hs, withDensity_apply _ hs, Measure.restrict_restrict hs]

theorem lintegral_hmeas {f : ℂ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict U)) :
    ∫⁻ z, f z ∂hmeas = ∫⁻ z in U, ENNReal.ofReal (1 / z.im ^ 2) * f z := by
  rw [hmeas_eq, lintegral_withDensity_eq_lintegral_mul₀]
  · rfl
  · exact (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun z : ℂ => 1 / z.im ^ 2)).aemeasurable
  · exact hf

theorem lintegral_flat_mob_meas (γ : SL(2, ℤ)) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z in U, ENNReal.ofReal (jac γ z) * g (mob γ z) = ∫⁻ z in U, g z := by
  set f : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (w.im ^ 2) * g w with hf
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun z : ℂ => z.im ^ 2)).mul hg
  have h1 := lintegral_mob γ hfm.aemeasurable
  rw [lintegral_hmeas (f := fun z => f (mob γ z)) (hfm.comp (measurable_mob γ)).aemeasurable, lintegral_hmeas hfm.aemeasurable] at h1
  have hL : ∫⁻ z in U, ENNReal.ofReal (jac γ z) * g (mob γ z) =
      ∫⁻ z in U, ENNReal.ofReal (1 / z.im ^ 2) * f (mob γ z) := by
    refine setLIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
    have hy : 0 < z.im := hz
    have e : (mob γ z).im ^ 2 = z.im ^ 2 * jac γ z := by
      rw [im_mob_eq γ hz]; unfold jac; ring
    simp only [hf]
    rw [e, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  have hR : ∫⁻ z in U, g z = ∫⁻ z in U, ENNReal.ofReal (1 / z.im ^ 2) * f z := by
    refine setLIntegral_congr_fun isOpen_U.measurableSet fun z hz => ?_
    have hy : 0 < z.im := hz
    simp only [hf]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have : 1 / z.im ^ 2 * z.im ^ 2 = 1 := by field_simp
    rw [this]; simp
  rw [hL, hR, h1]

theorem lintegral_flat_mob_meas' (γ : SL(2, ℤ)) {s : Set ℂ} (hs : MeasurableSet s) :
    ∫⁻ z in U, ENNReal.ofReal (jac γ z) * s.indicator 1 (mob γ z) = volume (s ∩ U) := by
  rw [lintegral_flat_mob_meas γ (measurable_one.indicator hs), lintegral_indicator_one hs]
  rw [Measure.restrict_apply hs]

theorem quasiMeasurePreserving_mob (γ : SL(2, ℤ)) :
    MeasureTheory.Measure.QuasiMeasurePreserving (mob γ) (volume.restrict U) (volume.restrict U) := by
  refine ⟨measurable_mob γ, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply (measurable_mob γ) hs]
  have h := lintegral_flat_mob_meas' γ hs
  rw [Measure.restrict_apply hs] at hs0
  rw [hs0] at h
  have hm : Measurable fun z => ENNReal.ofReal (jac γ z) * s.indicator (1 : ℂ → ℝ≥0∞) (mob γ z) :=
    (ENNReal.measurable_ofReal.comp (measurable_jac γ)).mul
      ((measurable_one.indicator hs).comp (measurable_mob γ))
  have h2 : ∀ᵐ z ∂(volume.restrict U), ENNReal.ofReal (jac γ z) * s.indicator 1 (mob γ z) = 0 :=
    (lintegral_eq_zero_iff hm).mp h
  have h3 : ∀ᵐ z ∂(volume.restrict U), mob γ z ∉ s := by
    filter_upwards [h2, ae_restrict_mem isOpen_U.measurableSet] with z hz hzU hzs
    have hpos : 0 < jac γ z := by
      unfold jac mobDeriv
      have : jfun γ z ≠ 0 := Partition.denom_ne_zero' γ hzU
      exact pow_pos (norm_pos_iff.mpr (one_div_ne_zero (pow_ne_zero 2 this))) 2
    have := hpos
    simp [hzs] at hz
    linarith
  have h4 := ae_iff.mp h3
  have h5 : mob γ ⁻¹' s = {a | ¬ mob γ a ∉ s} := by ext; simp
  rw [h5]
  exact h4

theorem lintegral_flat_mob (γ : SL(2, ℤ)) {g : ℂ → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict U)) :
    ∫⁻ z in U, ENNReal.ofReal (jac γ z) * g (mob γ z) = ∫⁻ z in U, g z := by
  have h1 : (fun z => ENNReal.ofReal (jac γ z) * g (mob γ z)) =ᵐ[volume.restrict U]
      fun z => ENNReal.ofReal (jac γ z) * hg.mk g (mob γ z) := by
    have := (quasiMeasurePreserving_mob γ).ae_eq_comp hg.ae_eq_mk
    filter_upwards [this] with z hz
    simp only [Function.comp_apply] at hz
    rw [hz]
  rw [lintegral_congr_ae h1, lintegral_flat_mob_meas γ hg.measurable_mk,
    lintegral_congr_ae hg.ae_eq_mk]

theorem map_mob_withDensity (γ : SL(2, ℤ)) :
    Measure.map (mob γ) ((volume.restrict U).withDensity fun z => ENNReal.ofReal (jac γ z)) =
      volume.restrict U := by
  ext s hs
  rw [Measure.map_apply (measurable_mob γ) hs, withDensity_apply _ (measurable_mob γ hs)]
  have h := lintegral_flat_mob_meas' γ hs
  rw [Measure.restrict_apply hs, ← h, ← lintegral_indicator (measurable_mob γ hs)]
  refine lintegral_congr fun z => ?_
  by_cases hz : mob γ z ∈ s <;> simp [Set.indicator, hz]

theorem integral_flat_mob {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (γ : SL(2, ℤ))
    {g : ℂ → E} (hg : AEStronglyMeasurable g (volume.restrict U)) :
    ∫ z in U, jac γ z • g (mob γ z) = ∫ z in U, g z := by
  have hmap := map_mob_withDensity γ
  have h1 : ∫ z, g z ∂(volume.restrict U) =
      ∫ z, g (mob γ z) ∂((volume.restrict U).withDensity fun z => ENNReal.ofReal (jac γ z)) := by
    rw [← integral_map (measurable_mob γ).aemeasurable (by rwa [hmap])]
    rw [hmap]
  have h2 := integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict U)
    (f := fun z => ENNReal.ofReal (jac γ z)) (ENNReal.measurable_ofReal.comp (measurable_jac γ))
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun z => g (mob γ z))
  rw [h1, h2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [ENNReal.toReal_ofReal (jac_nonneg γ z)]

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
