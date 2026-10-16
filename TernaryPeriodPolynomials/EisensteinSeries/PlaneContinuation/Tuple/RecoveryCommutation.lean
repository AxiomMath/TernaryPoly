module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.Ladder

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleLadder
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRecoveryCommutation

theorem toSmooth_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Function.Injective (toSmooth data index) := by
  intro first second equality
  funext key
  exact Subtype.ext (congrFun equality key)

theorem toSmooth_operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : Space data index) :
    toSmooth data index (operator data parameter halfPlane index value) =
      SmoothTupleOperator.operator data parameter (by linarith) (toSmooth data index value) := by
  funext key
  apply Subtype.ext
  exact congrFun ((operator_val data parameter halfPlane index value).trans
    (SmoothTupleOperator.operator_val data parameter (by linarith) (toSmooth data index value)).symm) key

theorem toSmooth_raising {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data index) :
    toSmooth data (index + 2) (modeRaising data index value) = raising data (toSmooth data index value) := rfl

theorem toSmooth_lowering {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data index) :
    toSmooth data (index - 2) (modeLowering data index value) = lowering data (toSmooth data index value) := rfl

theorem smooth_raising {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (value : SmoothTupleOperator.Space data) :
    SmoothTupleOperator.operator data parameter halfPlane (raising data value) =
      raising data (SmoothTupleOperator.operator data parameter halfPlane value) := by
  funext key
  simp only [SmoothTupleOperator.operator, SmoothTupleOperator.averagedRow, SmoothTupleOperator.projectedRow,
    raising, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    SmoothRecoveryEntries.operator, FiniteHilbertConvolution.smoothMap_raising, map_smul, map_sum]

theorem smooth_lowering {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (value : SmoothTupleOperator.Space data) :
    SmoothTupleOperator.operator data parameter halfPlane (lowering data value) =
      lowering data (SmoothTupleOperator.operator data parameter halfPlane value) := by
  funext key
  simp only [SmoothTupleOperator.operator, SmoothTupleOperator.averagedRow, SmoothTupleOperator.projectedRow,
    lowering, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    SmoothRecoveryEntries.operator, FiniteHilbertConvolution.smoothMap_lowering, map_smul, map_sum]

theorem mode_raising {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : Space data index) :
    modeRaising data index (operator data parameter halfPlane index value) =
      operator data parameter halfPlane (index + 2) (modeRaising data index value) := by
  apply toSmooth_injective data (index + 2)
  rw [toSmooth_raising, toSmooth_operator, toSmooth_operator, toSmooth_raising, smooth_raising]

theorem mode_lowering {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : Space data index) :
    modeLowering data index (operator data parameter halfPlane index value) =
      operator data parameter halfPlane (index - 2) (modeLowering data index value) := by
  apply toSmooth_injective data (index - 2)
  rw [toSmooth_lowering, toSmooth_operator, toSmooth_operator, toSmooth_lowering, smooth_lowering]

theorem restricted_raising {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : admissible data index) :
    admissibleRaising data index (restricted data parameter halfPlane index value) =
      restricted data parameter halfPlane (index + 2) (admissibleRaising data index value) :=
  Subtype.ext (mode_raising data parameter halfPlane index value.val)

theorem restricted_lowering {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (index : ℤ) (value : admissible data index) :
    admissibleLowering data index (restricted data parameter halfPlane index value) =
      restricted data parameter halfPlane (index - 2) (admissibleLowering data index value) :=
  Subtype.ext (mode_lowering data parameter halfPlane index value.val)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRecoveryCommutation
