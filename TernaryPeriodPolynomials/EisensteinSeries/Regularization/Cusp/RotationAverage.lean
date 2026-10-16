module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.BoundedCompactAnalyticAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspRotationAverage_integrable (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.H) :
    Integrable (fun angle => weight angle • cuspCircularOrbit cusp vector angle) AddCircle.haarAddCircle := by
  apply integrableOn_univ.mp
  exact ContinuousOn.integrableOn_compact isCompact_univ
    (weight.continuous.smul (cuspCircularOrbit_continuous cusp vector)).continuousOn

theorem cuspRotationAverage_integral_norm_le (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.H) :
    ‖∫ angle, weight angle • cuspCircularOrbit cusp vector angle ∂AddCircle.haarAddCircle‖ ≤ ‖weight‖ * ‖vector‖ := by
  calc
    _ ≤ ∫ angle, ‖weight angle • cuspCircularOrbit cusp vector angle‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ : AddCircle (1 : ℝ), ‖weight‖ * ‖vector‖ ∂AddCircle.haarAddCircle := by
      apply integral_mono (cuspRotationAverage_integrable cusp weight vector).norm (integrable_const _)
      intro angle
      dsimp only
      rw [norm_smul, cuspCircularOrbit_norm]
      exact mul_le_mul_of_nonneg_right (weight.norm_coe_le_norm angle) (norm_nonneg _)
    _ = _ := by simp

noncomputable def cuspRotationAverage (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) : cusp.H →L[ℂ] cusp.H :=
  LinearMap.mkContinuous
    { toFun := fun vector => ∫ angle, weight angle • cuspCircularOrbit cusp vector angle ∂AddCircle.haarAddCircle
      map_add' := fun first second => by
        simp only [cuspCircularOrbit_map_add, smul_add]
        exact integral_add (cuspRotationAverage_integrable cusp weight first) (cuspRotationAverage_integrable cusp weight second)
      map_smul' := fun scalar vector => by
        simp only [cuspCircularOrbit_map_smul, RingHom.id_apply]
        rw [← integral_smul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun angle => smul_comm _ _ _) }
    ‖weight‖ (cuspRotationAverage_integral_norm_le cusp weight)

theorem cuspRotationAverage_apply (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.H) :
    cuspRotationAverage cusp weight vector =
      ∫ angle, weight angle • cuspCircularOrbit cusp vector angle ∂AddCircle.haarAddCircle := rfl

noncomputable def cuspRotationKernelAction (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (angle : AddCircle (1 : ℝ)) : cusp.H →L[ℝ] cusp.H :=
  (weight angle • (cuspUnitaryAction cusp (atInfinity (binaryCircleRotation angle.toCircle))).toContinuousLinearMap).restrictScalars ℝ

theorem cuspRotationKernelAction_apply (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (angle : AddCircle (1 : ℝ)) (vector : cusp.H) :
    cuspRotationKernelAction cusp weight angle vector = weight angle • cuspCircularOrbit cusp vector angle := rfl

theorem cuspRotationKernelAction_norm_le (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (angle : AddCircle (1 : ℝ)) :
    ‖cuspRotationKernelAction cusp weight angle‖ ≤ ‖weight‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro vector
  rw [cuspRotationKernelAction_apply, norm_smul, cuspCircularOrbit_norm]
  exact mul_le_mul_of_nonneg_right (weight.norm_coe_le_norm angle) (norm_nonneg _)

theorem cuspRotationKernelAction_joint_continuous (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) :
    Continuous (fun input : AddCircle (1 : ℝ) × cusp.H => cuspRotationKernelAction cusp weight input.1 input.2) := by
  have rotation : Continuous (fun angle : AddCircle (1 : ℝ) => atInfinity (binaryCircleRotation angle.toCircle)) :=
    binary_atInfinity_continuous.comp (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle)
  change Continuous (fun input : AddCircle (1 : ℝ) × cusp.H =>
    weight input.1 • cusp.π (atInfinity (binaryCircleRotation input.1.toCircle)) input.2)
  exact (weight.continuous.comp continuous_fst).smul
    ((cusp_action_joint_continuous cusp).comp ((rotation.comp continuous_fst).prodMk continuous_snd))

theorem cuspRotationAverage_centeredOrbit_integral (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.H) (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    cuspCenteredMatrixOrbit cusp (cuspRotationAverage cusp weight vector) matrix =
      ∫ angle : AddCircle (1 : ℝ), cuspRotationKernelAction cusp weight angle
        (cuspCenteredMatrixOrbit cusp vector (binaryConjugationMap (binaryCircleRotation angle.toCircle) matrix))
        ∂AddCircle.haarAddCircle := by
  let action := (cuspUnitaryAction cusp (atInfinity (invertibleMatrix (1 + matrix)))).toContinuousLinearMap
  change action (∫ angle, weight angle • cuspCircularOrbit cusp vector angle ∂AddCircle.haarAddCircle) = _
  rw [← action.integral_comp_comm (cuspRotationAverage_integrable cusp weight vector)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro angle
  dsimp only
  rw [map_smul action, cuspRotationKernelAction_apply]
  change weight angle • cusp.π (atInfinity (invertibleMatrix (1 + matrix)))
      (cusp.π (atInfinity (binaryCircleRotation angle.toCircle)) vector) =
    weight angle • cusp.π (atInfinity (binaryCircleRotation angle.toCircle))
      (cusp.π (atInfinity (invertibleMatrix
        (1 + binaryConjugationMap (binaryCircleRotation angle.toCircle) matrix))) vector)
  simp only [← Module.End.mul_apply, ← map_mul, ← binary_atInfinity_mul, invertibleMatrix_one_add_conjugation]

theorem cuspRotationAverage_centeredOrbit_analyticAt (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.smooth) :
    AnalyticAt ℝ (cuspCenteredMatrixOrbit cusp (cuspRotationAverage cusp weight vector.val)) 0 := by
  obtain ⟨bound, bounded⟩ := binaryRotationConjugation_bounded
  have inner_continuous : ∀ vector : Matrix (Fin 2) (Fin 2) ℝ,
      Continuous (fun angle : AddCircle (1 : ℝ) => binaryConjugationMap (binaryCircleRotation angle.toCircle) vector) := by
    intro vector
    exact (binaryConjugationMap_continuous.comp
      (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle)).clm_apply continuous_const
  have integrated := compact_transformed_analyticAt_bounded AddCircle.haarAddCircle
    (cuspCenteredMatrixOrbit cusp vector.val) (cuspCenteredMatrixOrbit_analyticAt cusp vector)
    (fun angle : AddCircle (1 : ℝ) => binaryConjugationMap (binaryCircleRotation angle.toCircle))
    (cuspRotationKernelAction cusp weight) inner_continuous
    (cuspRotationKernelAction_joint_continuous cusp weight) bound ‖weight‖₊ bounded
    (cuspRotationKernelAction_norm_le cusp weight)
  exact integrated.congr (Filter.Eventually.of_forall
    (fun matrix => (cuspRotationAverage_centeredOrbit_integral cusp weight vector.val matrix).symm))

theorem cuspRotationAverage_finite_fixed (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.H) (matrix : BinaryFiniteGL)
    (fixed : cusp.π (atFinite matrix) vector = vector) :
    cusp.π (atFinite matrix) (cuspRotationAverage cusp weight vector) = cuspRotationAverage cusp weight vector := by
  let action := (cuspUnitaryAction cusp (atFinite matrix)).toContinuousLinearMap
  change action (∫ angle, weight angle • cuspCircularOrbit cusp vector angle ∂AddCircle.haarAddCircle) = _
  rw [← action.integral_comp_comm (cuspRotationAverage_integrable cusp weight vector)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro angle
  dsimp only
  rw [map_smul action]
  congr 1
  change cusp.π (atFinite matrix) (cusp.π (atInfinity (binaryCircleRotation angle.toCircle)) vector) =
    cusp.π (atInfinity (binaryCircleRotation angle.toCircle)) vector
  rw [← Module.End.mul_apply, ← map_mul, ← binary_atInfinity_atFinite_commute, map_mul, Module.End.mul_apply, fixed]

theorem cuspRotationAverage_mem_smooth (cusp : CuspidalRepresentation)
    (weight : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.smooth) :
    cuspRotationAverage cusp weight vector.val ∈ cusp.smooth := by
  apply (cusp.smooth_exact _).mpr
  refine ⟨cuspRealOrbit_smooth_of_centered cusp _ (cuspRotationAverage_centeredOrbit_analyticAt cusp weight vector), ?_⟩
  obtain ⟨level, level_open, level_compact, fixed⟩ := ((cusp.smooth_exact vector.val).mp vector.property).2
  exact ⟨level, level_open, level_compact, fun binary =>
    cuspRotationAverage_finite_fixed cusp weight vector.val binary.val (fixed binary)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
