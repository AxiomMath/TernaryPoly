module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.TranslatedSeries
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PackedSeries

@[expose] public section


open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedAnalytic

open TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries

variable {Domain Target : Type}
variable [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem coefficient_norm_bound (series : FormalMultilinearSeries ℝ Domain Target)
    (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (order additional : ℕ) :
    ‖(coefficientRadius : ℝ) ^ order • series.changeOriginSeries order additional‖ *
      (shiftRadius : ℝ) ^ additional ≤ (originMajorant series shiftRadius coefficientRadius order : ℝ) := by
  let _ : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) Target) := inferInstance
  have shiftBound : (shiftRadius : ENNReal) < series.radius :=
    (le_add_right le_rfl).trans_lt radiusBound
  have summable : Summable (fun index : OriginIndices order =>
      ‖series (order + index.1)‖₊ * shiftRadius ^ index.1 * coefficientRadius ^ order) :=
    (series.changeOriginSeries_summable_aux₂ shiftBound order).mul_right _
  have fiberBound : (∑' index : {indices : Finset (Fin (order + additional)) // indices.card = additional},
      ‖series (order + additional)‖₊ * shiftRadius ^ additional * coefficientRadius ^ order) ≤
      originMajorant series shiftRadius coefficientRadius order := by
    apply Summable.tsum_le_tsum_of_inj (fun index => Sigma.mk additional index)
    · intro first second equality
      exact eq_of_heq (Sigma.mk.inj_iff.mp equality).2
    · intro index _
      exact zero_le
    · intro index
      exact le_rfl
    · exact (hasSum_fintype _).summable
    · exact summable
  have bound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (series.nnnorm_changeOriginSeries_le_tsum order additional)
      (show (0 : ℝ≥0) ≤ shiftRadius ^ additional from zero_le))
    (show (0 : ℝ≥0) ≤ coefficientRadius ^ order from zero_le)
  rw [← NNReal.tsum_mul_right, ← NNReal.tsum_mul_right] at bound
  have realBound : ‖series.changeOriginSeries order additional‖ * (shiftRadius : ℝ) ^ additional *
      (coefficientRadius : ℝ) ^ order ≤ (originMajorant series shiftRadius coefficientRadius order : ℝ) := by
    exact_mod_cast bound.trans fiberBound
  have scaledBound :
      ‖(coefficientRadius : ℝ) ^ order • series.changeOriginSeries order additional‖ ≤
        (coefficientRadius : ℝ) ^ order * ‖series.changeOriginSeries order additional‖ := by
    apply le_trans (norm_smul_le ((coefficientRadius : ℝ) ^ order)
      (series.changeOriginSeries order additional))
    exact le_of_eq (congrArg (fun scalar : ℝ => scalar * ‖series.changeOriginSeries order additional‖)
      (Real.norm_of_nonneg (pow_nonneg coefficientRadius.property order)))
  calc
    _ ≤ ((coefficientRadius : ℝ) ^ order * ‖series.changeOriginSeries order additional‖) *
        (shiftRadius : ℝ) ^ additional :=
      mul_le_mul_of_nonneg_right scaledBound (pow_nonneg shiftRadius.property additional)
    _ = ‖series.changeOriginSeries order additional‖ * (shiftRadius : ℝ) ^ additional *
        (coefficientRadius : ℝ) ^ order := by ring
    _ ≤ _ := realBound

def family (series : FormalMultilinearSeries ℝ Domain Target)
    (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : Domain) :
    lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) Target) ⊤ :=
  if membership : ‖offset‖₊ ≤ shiftRadius then
    translatedCoefficients series shiftRadius coefficientRadius radiusBound ⟨offset, membership⟩
  else 0

theorem family_apply (series : FormalMultilinearSeries ℝ Domain Target)
    (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : Domain) (membership : ‖offset‖₊ ≤ shiftRadius) (order : ℕ) :
    family series shiftRadius coefficientRadius radiusBound offset order =
      (coefficientRadius : ℝ) ^ order • series.changeOrigin offset order := by
  simp only [family, dite_eq_left membership, translatedCoefficients_apply]

variable [CompleteSpace Target]

theorem family_hasFPowerSeries (series : FormalMultilinearSeries ℝ Domain Target)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveShift : 0 < shiftRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    HasFPowerSeriesOnBall (family series shiftRadius coefficientRadius radiusBound)
      (PackedSeries.series (fun order => (coefficientRadius : ℝ) ^ order • series.changeOriginSeries order))
      0 shiftRadius := by
  let _ : ∀ order : ℕ, CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) Target) :=
    fun _ => ContinuousMultilinearMap.instCompleteSpace
  have shiftBound : (shiftRadius : ENNReal) < series.radius :=
    (le_add_right le_rfl).trans_lt radiusBound
  have positive : (0 : ENNReal) < shiftRadius := by exact_mod_cast positiveShift
  apply PackedSeries.hasFPowerSeries _ _ shiftRadius positiveShift
    (fun order => (originMajorant series shiftRadius coefficientRadius order : ℝ))
    (NNReal.summable_coe.mpr (originMajorant_summable series shiftRadius coefficientRadius radiusBound))
    (coefficient_norm_bound series shiftRadius coefficientRadius radiusBound)
  intro order
  apply (((series.hasFPowerSeriesOnBall_changeOrigin order (positive.trans shiftBound)).mono
    positive shiftBound.le).const_smul (c := (coefficientRadius : ℝ) ^ order)).congr
  intro offset membership
  have offsetBound : ‖offset‖₊ ≤ shiftRadius := by
    have strict : ‖offset‖₊ < shiftRadius := by
      simpa only [Metric.mem_eball, edist_lt_coe, nndist_zero_right] using membership
    exact strict.le
  exact (family_apply series shiftRadius coefficientRadius radiusBound offset offsetBound order).symm

theorem family_analyticOnNhd (series : FormalMultilinearSeries ℝ Domain Target)
    (shiftRadius coefficientRadius : ℝ≥0) (positiveShift : 0 < shiftRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    AnalyticOnNhd ℝ (family series shiftRadius coefficientRadius radiusBound)
      (Metric.eball 0 (shiftRadius : ENNReal)) :=
  (family_hasFPowerSeries series shiftRadius coefficientRadius positiveShift radiusBound).analyticOnNhd

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedAnalytic
