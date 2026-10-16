module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlagParameterBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem realPlaneHeight_continuous : Continuous realPlaneHeight := by
  have matrix_continuous : Continuous (Units.val : RealGL3 → Matrix (Fin 3) (Fin 3) ℝ) :=
    Units.continuous_val
  have entry_continuous (row column : Fin 3) : Continuous (fun matrix : RealGL3 => matrix.val row column) :=
    (continuous_apply column).comp ((continuous_apply row).comp matrix_continuous)
  exact (((entry_continuous 2 0).pow 2 |>.add ((entry_continuous 2 1).pow 2)).add
    ((entry_continuous 2 2).pow 2)).sqrt

theorem planeParameterWeight_continuous : Continuous planeParameterWeight := by
  have determinant_norm : Continuous (fun matrix : AdelicGL =>
      (adeleNorm (GeneralLinearGroup.det matrix) : ℝ)) :=
    NNReal.continuous_coe.comp (adeleNorm_continuous.comp adelicDet_continuous)
  have logarithm_continuous := determinant_norm.log (fun matrix =>
    ne_of_gt (NNReal.coe_pos.mpr (adeleNorm_pos (GeneralLinearGroup.det matrix))))
  exact (logarithm_continuous.div_const 3).sub
    ((realPlaneHeight_continuous.comp realGroup_continuous).log
      (fun matrix => ne_of_gt (realPlaneHeight_pos (realGroup matrix))))

theorem finiteIntegralGL_isOpen :
    IsOpen (Set.range (GeneralLinearGroup.map (n := Fin 3) integralEmbedding)) := by
  simpa only [Set.image_univ] using
    generalLinearGroup_map_isOpen integralEmbedding integralEmbedding_isOpenEmbedding 3 Set.univ isOpen_univ

theorem flat_section_joint_continuous_integral
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family) :
    ContinuousOn (fun input : ℂ × AdelicGL => family input.1 input.2)
      {input | finiteGroup input.2 ∈ Set.range (GeneralLinearGroup.map integralEmbedding)} := by
  have model : Continuous (fun input : ℂ × AdelicGL =>
      Complex.exp ((input.1 - cohomologicalPoint) * (planeParameterWeight input.2 : ℂ)) *
        family cohomologicalPoint input.2) :=
    (((continuous_fst.sub continuous_const).mul
      (Complex.continuous_ofReal.comp (planeParameterWeight_continuous.comp continuous_snd))).cexp).mul
      ((induced_continuous (flat.1 cohomologicalPoint)).comp continuous_snd)
  apply model.continuousOn.congr
  intro input integral
  exact flat_section_integral_finite_scaling flat input.1 input.2 integral

theorem flat_section_joint_continuousAt_integral
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (parameter : ℂ) (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ContinuousAt (fun input : ℂ × AdelicGL => family input.1 input.2) (parameter, matrix) := by
  exact ((finiteIntegralGL_isOpen.preimage (finiteGroup_continuous.comp continuous_snd)).continuousOn_iff.mp
    (flat_section_joint_continuous_integral flat)) integral

theorem flat_section_compact_parameter_matrix_bound
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (integral : ∀ matrix ∈ matrices,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
      ‖family parameter matrix‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := (parameters_compact.prod matrices_compact).exists_bound_of_continuousOn
    ((flat_section_joint_continuous_integral flat).mono (fun input member => integral input.2 member.2))
  exact ⟨max 0 bound, le_max_left _ _, fun parameter parameter_in matrix matrix_in =>
    (bounded (parameter, matrix) ⟨parameter_in, matrix_in⟩).trans (le_max_right _ _)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
