module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.FriedrichsDomination
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.FriedrichsPointwise
public import TernaryPeriodPolynomials.Analysis.Compact.DominatedSquareConvergence

@[expose] public section


/-! Genuine L2 convergence of the actual first-order Friedrichs commutator on compact C1 inputs. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory Filter ScalarFriedrichsEnvelope ScaledScalarKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The actual first-order commutator converges in square integral, with all domination and
common compact support obligations proved from the genuine kernel and input. -/
theorem firstOrder_convolution_commutator_integral_tendsto (κ a b f : E → ℝ) (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hκ : ContDiff ℝ 1 κ) (hcf : HasCompactSupport f) (hcκ : HasCompactSupport κ)
    (hκnonneg : ∀ y, 0 ≤ κ y) (hmass : ∫ y, κ y ∂μ = 1)
    (L A B : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haL : ∀ x y, ‖a x - a y‖ ≤ L * ‖x-y‖)
    (hda : ∀ y, ‖fderiv ℝ a y v‖ ≤ A) (hbB : ∀ y, ‖b y‖ ≤ B) :
    Tendsto (fun c : ℝ => ∫ x, ‖firstOrder v a b (scalarConvolution μ (dilate c κ) f) x -
      scalarConvolution μ (dilate c κ) (firstOrder v a b f) x‖ ^ 2 ∂μ) atTop (nhds 0) := by
  let k := envelope κ v L A B
  let u (c : ℝ) (x : E) := firstOrder v a b (scalarConvolution μ (dilate c κ) f) x -
    scalarConvolution μ (dilate c κ) (firstOrder v a b f) x
  have hk : Continuous k := continuous_envelope κ v L A B hκ
  have hck : HasCompactSupport k := compact_envelope κ v L A B hcκ
  have hkn (z : E) : 0 ≤ k z := envelope_nonneg κ v z L A B hL hA hB
  obtain ⟨R, _, hR⟩ := hck.exists_pos_le_norm
  obtain ⟨S, _, hS⟩ := hcf.exists_pos_le_norm
  have hks : Function.support k ⊆ Metric.closedBall 0 R := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (lt_of_not_ge (fun hzR => hz (hR z hzR))).le
  have hfs : Function.support (fun z => ‖f z‖) ⊆ Metric.closedBall 0 S := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (lt_of_not_ge (fun hzS => hz (by simp [hS z hzS]))).le
  obtain ⟨F, hF⟩ := (hcf.isCompact_range hf.continuous).isBounded.exists_norm_le
  have hfF (y : E) : ‖f y‖ ≤ F := hF _ ⟨y, rfl⟩
  have hFpos : 0 ≤ F := (norm_nonneg (f 0)).trans (hfF 0)
  let M := ∫ z, k z ∂μ
  have hM : 0 ≤ M := integral_nonneg hkn
  have hdom (c : ℝ) (hc : 1 ≤ c) (x : E) : ‖u c x‖ ≤
      scalarConvolution μ (dilate c k) (fun y => ‖f y‖) x :=
    norm_firstOrder_commutator_dilate_le_envelope μ κ a b f v x ha hb hf hκ hcf hcκ
      L A B (haL x) hda hbB c (by linarith)
  have hbound (c : ℝ) (hc : 1 ≤ c) (x : E) : ‖u c x‖ ≤ M * F := by
    have hcpos : 0 < c := by linarith
    have hki : Integrable (dilate c k) μ :=
      (continuous_const.mul (hk.comp (continuous_const.smul continuous_id))).integrable_of_hasCompactSupport
        (compact_dilate k c hcpos.ne' hck)
    have hn := norm_scalarConvolution_le_mass μ (dilate c k) (fun y => ‖f y‖) hki
      (nonneg_dilate k c hcpos.le hkn) F (fun y => by simpa only [norm_norm] using hfF y) x
    rw [integral_dilate μ c hcpos] at hn
    exact (hdom c hc x).trans ((le_abs_self _).trans hn)
  have hsupp (c : ℝ) (hc : 1 ≤ c) (x : E) (hx : x ∉ Metric.closedBall 0 (S+R)) : u c x = 0 := by
    have hzero : scalarConvolution μ (dilate c k) (fun y => ‖f y‖) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hx
        (tsupport_scalarConvolution_dilate_subset μ k (fun y => ‖f y‖) R S c hc hks hfs hh))
    have h := hdom c hc x
    rw [hzero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hcont (c : ℝ) (hc : 1 ≤ c) : Continuous (u c) := by
    have hcpos : 0 < c := by linarith
    have hkd := contDiff_dilate κ c hκ
    have hkcd := compact_dilate κ c hcpos.ne' hcκ
    exact (continuous_firstOrder v ha.continuous hb
      (contDiff_scalarConvolution μ _ f hkd hkcd hf.continuous)).sub
      (contDiff_scalarConvolution μ _ (firstOrder v a b f) hkd hkcd
        (continuous_firstOrder v ha.continuous hb hf)).continuous
  apply CompactDominatedSquareConvergence.integral_norm_square_tendsto_zero u
    (Metric.closedBall 0 (S+R)) Metric.isClosed_closedBall.measurableSet
    (isCompact_closedBall (0 : E) (S+R)).measure_lt_top.ne (M*F) (mul_nonneg hM hFpos)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    exact (hcont c hc).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    exact hbound c hc
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    exact hsupp c hc
  · intro x
    exact firstOrder_convolution_commutator_tendsto μ κ a b f v x hκ hcκ hκnonneg hmass
      ha.continuous hb hf hcf

end TernaryPoly.CompactCoordinateIntegration
