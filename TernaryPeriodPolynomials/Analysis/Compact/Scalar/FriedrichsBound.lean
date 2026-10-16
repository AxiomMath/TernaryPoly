module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Friedrichs
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity
public import TernaryPeriodPolynomials.Analysis.Scalar.FriedrichsEnvelopeRegularity
public import TernaryPeriodPolynomials.Analysis.DominatedKernelSquareBound

@[expose] public section


/-! An actual L2 bound for the full variable-coefficient first-order convolution commutator. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory ScalarFriedrichsEnvelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The complete first-order commutator is bounded in L2 by its genuine kernel mass.
All integrability obligations are discharged from smoothness and compact support. -/
theorem firstOrder_convolution_commutator_square_bound (κ a b f : E → ℝ) (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hκ : ContDiff ℝ 1 κ) (hcf : HasCompactSupport f) (hcκ : HasCompactSupport κ)
    (L A B : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haL : ∀ x y, ‖a x - a y‖ ≤ L * ‖x-y‖)
    (hda : ∀ y, ‖fderiv ℝ a y v‖ ≤ A) (hbB : ∀ y, ‖b y‖ ≤ B) :
    ∫ x, ‖firstOrder v a b (scalarConvolution μ κ f) x -
        scalarConvolution μ κ (firstOrder v a b f) x‖ ^ 2 ∂μ ≤
      (∫ z, envelope κ v L A B z ∂μ) ^ 2 * ∫ y, ‖f y‖ ^ 2 ∂μ := by
  let k := envelope κ v L A B
  have hk : Continuous k := continuous_envelope κ v L A B hκ
  have hck : HasCompactSupport k := compact_envelope κ v L A B hcκ
  have hki : Integrable k μ := hk.integrable_of_hasCompactSupport hck
  have hkn (z : E) : 0 ≤ k z := envelope_nonneg κ v z L A B hL hA hB
  have hgi : Integrable (fun y => ‖f y‖ ^ 2) μ :=
    (hf.continuous.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] using hcf.norm.mul_right (f' := fun y => ‖f y‖))
  have h0 (x : E) : Integrable (fun y => k (x-y)) μ := hki.comp_sub_left x
  have h1 (x : E) : Integrable (fun y => k (x-y) * ‖f y‖) μ :=
    ((hk.comp (continuous_const.sub continuous_id)).mul hf.continuous.norm).integrable_of_hasCompactSupport
      hcf.norm.mul_left
  have h2 (x : E) : Integrable (fun y => k (x-y) * ‖f y‖ ^ 2) μ :=
    ((hk.comp (continuous_const.sub continuous_id)).mul (hf.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] using (hcf.norm.mul_right (f' := fun y => ‖f y‖)).mul_left (f := fun y => k (x-y)))
  have hp : Integrable (fun p : E × E => k (p.1-p.2) * ‖f p.2‖ ^ 2) (μ.prod μ) := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      hgi.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hki
  have hconv := contDiff_scalarConvolution μ κ f hκ hcκ hf.continuous
  have hcconv := compact_scalarConvolution μ κ f hcκ hcf
  have hdf := continuous_firstOrder v ha.continuous hb hf
  have hcdf := compact_firstOrder v a b hcf
  have hconvdf : Continuous (scalarConvolution μ κ (firstOrder v a b f)) :=
    (contDiff_scalarConvolution μ κ (firstOrder v a b f) hκ hcκ hdf).continuous
  have hout : Integrable (fun x => ‖firstOrder v a b (scalarConvolution μ κ f) x -
      scalarConvolution μ κ (firstOrder v a b f) x‖ ^ 2) μ := by
    have hc := (compact_firstOrder v a b hcconv).sub
      (compact_scalarConvolution μ κ (firstOrder v a b f) hcκ hcdf)
    apply (((continuous_firstOrder v ha.continuous hb hconv).sub hconvdf).norm.pow 2).integrable_of_hasCompactSupport
    simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] using hc.norm.mul_right (f' := fun x => ‖firstOrder v a b (scalarConvolution μ κ f) x - scalarConvolution μ κ (firstOrder v a b f) x‖)
  have hT (x : E) : ‖firstOrder v a b (scalarConvolution μ κ f) x -
      scalarConvolution μ κ (firstOrder v a b f) x‖ ≤ ∫ y, k (x-y) * ‖f y‖ ∂μ := by
    rw [firstOrder_convolution_commutator μ κ a b f v x ha hb hf hκ hcf hcκ]
    apply norm_integral_le_of_norm_le (h1 x)
    exact Filter.Eventually.of_forall (fun y => by
      rw [norm_mul]
      calc
        _ ≤ ‖f y‖ * k (x-y) := mul_le_mul_of_nonneg_left
          (norm_commutatorKernel_le κ a b v x y L A B (haL x y) (hda y) (hbB x) (hbB y)) (norm_nonneg _)
        _ = _ := mul_comm _ _)
  have hh := KernelSquareBound.integral_norm_square_le_of_dominated
    (fun x y => k (x-y)) (fun y => ‖f y‖)
    (fun x => firstOrder v a b (scalarConvolution μ κ f) x - scalarConvolution μ κ (firstOrder v a b f) x)
    (fun x y => hkn (x-y)) (fun y => norm_nonneg (f y))
    (∫ z, k z ∂μ) (∫ z, k z ∂μ) (integral_nonneg hkn)
    (fun x => (integral_sub_left_eq_self k μ x).le)
    (fun y => (integral_sub_right_eq_self k y).le) h0 h1 h2 hp hgi hout hT
  simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] using hh

end TernaryPoly.CompactCoordinateIntegration
