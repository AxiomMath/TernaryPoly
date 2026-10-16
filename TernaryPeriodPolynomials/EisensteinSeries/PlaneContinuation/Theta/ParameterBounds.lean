module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.SchwartzTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaParameterBounds

abbrev Parameter := AdelicGL × BinaryAdelicGL

noncomputable def realAction (parameter : Parameter) : RealSpace ≃L[ℝ] RealSpace :=
  realTransform (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) parameter.1)
    (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) parameter.2)

noncomputable def finiteAction (parameter : Parameter) : Rectangular FiniteAdeles ≃ₜ Rectangular FiniteAdeles :=
  matrixHomeomorph (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) parameter.1)
    (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) parameter.2)

theorem matrix_fst_continuous {rows columns : Type*} :
    Continuous (fun matrix : Matrix rows columns Adeles => matrix.map (RingHom.fst ℝ FiniteAdeles)) :=
  continuous_pi (fun row => continuous_pi (fun column =>
    continuous_fst.comp ((continuous_apply column).comp (continuous_apply row))))

theorem matrix_snd_continuous {rows columns : Type*} :
    Continuous (fun matrix : Matrix rows columns Adeles => matrix.map (RingHom.snd ℝ FiniteAdeles)) :=
  continuous_pi (fun row => continuous_pi (fun column =>
    continuous_snd.comp ((continuous_apply column).comp (continuous_apply row))))

theorem realAction_inverse_continuous :
    Continuous (fun parameter : Parameter => (realAction parameter).symm.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro vector
  change Continuous (fun parameter : Parameter => coordinateEquiv
    (parameter.1.val.map (RingHom.fst ℝ FiniteAdeles) * coordinateEquiv.symm vector *
      parameter.2⁻¹.val.map (RingHom.fst ℝ FiniteAdeles)))
  exact coordinateEquiv.toContinuousLinearEquiv.continuous.comp
    (((matrix_fst_continuous.comp (Units.continuous_val.comp continuous_fst)).matrix_mul continuous_const).matrix_mul
      (matrix_fst_continuous.comp (Units.continuous_val.comp continuous_snd.inv)))

theorem exists_distortion_bound (parameters : Set Parameter) (compact : IsCompact parameters) :
    ∃ distortion : ℝ, 0 ≤ distortion ∧ ∀ parameter ∈ parameters, ∀ vector : RealSpace,
      ‖vector‖ ≤ distortion * ‖realAction parameter vector‖ := by
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn realAction_inverse_continuous.continuousOn
  refine ⟨max bound 0, le_max_right _ _, fun parameter membership vector => ?_⟩
  calc
    ‖vector‖ = ‖(realAction parameter).symm (realAction parameter vector)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖(realAction parameter).symm.toContinuousLinearMap‖ * ‖realAction parameter vector‖ :=
      (realAction parameter).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ max bound 0 * ‖realAction parameter vector‖ :=
      mul_le_mul_of_nonneg_right ((bounded parameter membership).trans (le_max_left _ _)) (norm_nonneg _)

theorem finiteAction_inverse_continuous :
    Continuous (fun pair : Parameter × Rectangular FiniteAdeles => (finiteAction pair.1).symm pair.2) := by
  change Continuous (fun pair : Parameter × Rectangular FiniteAdeles =>
    pair.1.1.val.map (RingHom.snd ℝ FiniteAdeles) * pair.2 *
      pair.1.2⁻¹.val.map (RingHom.snd ℝ FiniteAdeles))
  exact ((matrix_snd_continuous.comp (Units.continuous_val.comp (continuous_fst.comp continuous_fst))).matrix_mul
    continuous_snd).matrix_mul
      (matrix_snd_continuous.comp (Units.continuous_val.comp (continuous_snd.comp continuous_fst).inv))

theorem exists_finite_hull (finiteTest : Rectangular FiniteAdeles → ℂ)
    (compactSupport : HasCompactSupport finiteTest) (parameters : Set Parameter) (compact : IsCompact parameters) :
    ∃ hull : Set (Rectangular FiniteAdeles), IsCompact hull ∧ ∀ parameter ∈ parameters,
      ∀ matrix : Rectangular FiniteAdeles, finiteTest (finiteAction parameter matrix) ≠ 0 → matrix ∈ hull := by
  let hull := (fun pair : Parameter × Rectangular FiniteAdeles => (finiteAction pair.1).symm pair.2) ''
    (parameters ×ˢ tsupport finiteTest)
  refine ⟨hull, (compact.prod compactSupport).image finiteAction_inverse_continuous, ?_⟩
  intro parameter membership matrix nonzero
  exact ⟨(parameter, finiteAction parameter matrix), ⟨membership, subset_closure nonzero⟩,
    (finiteAction parameter).symm_apply_apply matrix⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaParameterBounds
