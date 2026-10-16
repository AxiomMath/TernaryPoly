module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.RotationConjugation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspRotationWeightedAction (cusp : CuspidalRepresentation) (weight : ℤ)
    (angle : AddCircle (1 : ℝ)) : cusp.H →L[ℝ] cusp.H :=
  ((fourier (-weight) angle) •
    (cuspUnitaryAction cusp (atInfinity (binaryCircleRotation angle.toCircle))).toContinuousLinearMap).restrictScalars ℝ

theorem cuspRotationWeightedAction_apply (cusp : CuspidalRepresentation) (weight : ℤ)
    (angle : AddCircle (1 : ℝ)) (vector : cusp.H) :
    cuspRotationWeightedAction cusp weight angle vector = fourier (-weight) angle • cuspCircularOrbit cusp vector angle := rfl

theorem cuspRotationWeightedAction_norm_le (cusp : CuspidalRepresentation) (weight : ℤ)
    (angle : AddCircle (1 : ℝ)) : ‖cuspRotationWeightedAction cusp weight angle‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro vector
  simp only [cuspRotationWeightedAction_apply, norm_smul, circle_fourier_norm, cuspCircularOrbit_norm, one_mul, le_refl]

theorem cuspRotationWeightedAction_joint_continuous (cusp : CuspidalRepresentation) (weight : ℤ) :
    Continuous (fun input : AddCircle (1 : ℝ) × cusp.H => cuspRotationWeightedAction cusp weight input.1 input.2) := by
  have rotation : Continuous (fun angle : AddCircle (1 : ℝ) => atInfinity (binaryCircleRotation angle.toCircle)) :=
    binary_atInfinity_continuous.comp (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle)
  change Continuous (fun input : AddCircle (1 : ℝ) × cusp.H =>
    fourier (-weight) input.1 • cusp.π (atInfinity (binaryCircleRotation input.1.toCircle)) input.2)
  exact ((fourier (-weight)).continuous.comp continuous_fst).smul
    ((cusp_action_joint_continuous cusp).comp ((rotation.comp continuous_fst).prodMk continuous_snd))

noncomputable def cuspCenteredMatrixOrbit (cusp : CuspidalRepresentation) (vector : cusp.H)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) : cusp.H :=
  cusp.π (atInfinity (invertibleMatrix (1 + matrix))) vector

theorem cuspCenteredMatrixOrbit_analyticAt (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    AnalyticAt ℝ (cuspCenteredMatrixOrbit cusp vector.val) 0 := by
  have original : AnalyticAt ℝ (cuspMatrixOrbit cusp vector) (1 + (0 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    simpa only [add_zero, Units.val_one] using (cuspMatrixOrbit_contDiffAt cusp vector 1).analyticAt
  exact original.comp (analyticAt_const.add analyticAt_id)

theorem cuspRotationProjection_centeredOrbit_integral (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H) (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    cuspCenteredMatrixOrbit cusp (cuspRotationProjection cusp weight vector) matrix =
      ∫ angle : AddCircle (1 : ℝ), cuspRotationWeightedAction cusp weight angle
        (cuspCenteredMatrixOrbit cusp vector (binaryConjugationMap (binaryCircleRotation angle.toCircle) matrix))
        ∂AddCircle.haarAddCircle := by
  let action := (cuspUnitaryAction cusp (atInfinity (invertibleMatrix (1 + matrix)))).toContinuousLinearMap
  change action (∫ angle : AddCircle (1 : ℝ), fourier (-weight) angle • cuspCircularOrbit cusp vector angle
    ∂AddCircle.haarAddCircle) = _
  rw [← action.integral_comp_comm (cuspRotationFourier_integrable cusp weight vector)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro angle
  dsimp only
  rw [map_smul action, cuspRotationWeightedAction_apply]
  change fourier (-weight) angle •
      cusp.π (atInfinity (invertibleMatrix (1 + matrix)))
        (cusp.π (atInfinity (binaryCircleRotation angle.toCircle)) vector) =
    fourier (-weight) angle • cusp.π (atInfinity (binaryCircleRotation angle.toCircle))
      (cusp.π (atInfinity (invertibleMatrix
        (1 + binaryConjugationMap (binaryCircleRotation angle.toCircle) matrix))) vector)
  simp only [← Module.End.mul_apply, ← map_mul, ← binary_atInfinity_mul,
    invertibleMatrix_one_add_conjugation]

theorem cuspRotationProjection_centeredOrbit_analyticAt (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) :
    AnalyticAt ℝ (cuspCenteredMatrixOrbit cusp (cuspRotationProjection cusp weight vector.val)) 0 := by
  obtain ⟨bound, bounded⟩ := binaryRotationConjugation_bounded
  have inner_continuous : ∀ vector : Matrix (Fin 2) (Fin 2) ℝ,
      Continuous (fun angle : AddCircle (1 : ℝ) => binaryConjugationMap (binaryCircleRotation angle.toCircle) vector) := by
    intro vector
    exact (binaryConjugationMap_continuous.comp
      (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle)).clm_apply continuous_const
  have integrated := compact_transformed_analyticAt AddCircle.haarAddCircle
    (cuspCenteredMatrixOrbit cusp vector.val) (cuspCenteredMatrixOrbit_analyticAt cusp vector)
    (fun angle : AddCircle (1 : ℝ) => binaryConjugationMap (binaryCircleRotation angle.toCircle))
    (cuspRotationWeightedAction cusp weight) inner_continuous
    (cuspRotationWeightedAction_joint_continuous cusp weight) bound bounded
    (cuspRotationWeightedAction_norm_le cusp weight)
  exact integrated.congr (Filter.Eventually.of_forall
    (fun matrix => (cuspRotationProjection_centeredOrbit_integral cusp weight vector.val matrix).symm))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
