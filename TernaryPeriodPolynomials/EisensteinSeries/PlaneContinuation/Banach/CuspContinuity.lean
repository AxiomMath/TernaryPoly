module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.CuspDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.FunctionContinuity
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachCuspDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachCuspContinuity

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

def continuousRealizationLinear {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) :
    Source →ₗ[ℂ] BoundedContinuousFunction BinaryAdelicGL ℂ where
  toFun vector := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun point => evaluation data family continuous point vector)
    (CuspFunctionContinuity.continuous data.cusp (family vector).val)
    (‖realization data family continuous‖ * ‖vector‖)
    (fun point => ((evaluation data family continuous point).le_opNorm vector).trans
      (mul_le_mul_of_nonneg_right (evaluation_norm_bound data family continuous point) (norm_nonneg vector)))
  map_add' first second := by
    ext point
    exact map_add (evaluation data family continuous point) first second
  map_smul' scalar vector := by
    ext point
    exact map_smul (evaluation data family continuous point) scalar vector

def continuousRealization {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) :
    Source →L[ℂ] BoundedContinuousFunction BinaryAdelicGL ℂ :=
  (continuousRealizationLinear data family continuous).mkContinuous ‖realization data family continuous‖
    (fun vector => (BoundedContinuousFunction.norm_le
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (fun point =>
        ((evaluation data family continuous point).le_opNorm vector).trans
          (mul_le_mul_of_nonneg_right (evaluation_norm_bound data family continuous point) (norm_nonneg vector))))

theorem continuousRealization_apply {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) (vector : Source) (point : BinaryAdelicGL) :
    continuousRealization data family continuous vector point = data.cusp.realize (family vector).val point := rfl

theorem joint_continuous {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val)) :
    Continuous (fun pair : Source × BinaryAdelicGL => data.cusp.realize (family pair.1).val pair.2) :=
  ContinuousEval.continuous_eval.comp
    (((continuousRealization data family continuous).continuous.comp continuous_fst).prodMk continuous_snd)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachCuspContinuity
