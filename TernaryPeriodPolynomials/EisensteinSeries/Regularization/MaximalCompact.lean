module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.GlobalSectionContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem real_orthogonal_entry_bound {matrix : RealGL3}
    (orthogonal : matrix.val.transpose * matrix.val = 1) (row column : Fin 3) :
    ‖matrix.val row column‖ ≤ 1 := by
  have column_norm : ∑ index : Fin 3, matrix.val index column ^ 2 = 1 := by
    simpa [Matrix.mul_apply, pow_two] using
      congrArg (fun value : Matrix (Fin 3) (Fin 3) ℝ => value column column) orthogonal
  have entry_bound := Finset.single_le_sum (fun index (_ : index ∈ (Finset.univ : Finset (Fin 3))) =>
    sq_nonneg (matrix.val index column)) (Finset.mem_univ row)
  rw [column_norm] at entry_bound
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

theorem real_orthogonal_inverse {matrix : RealGL3}
    (orthogonal : matrix.val.transpose * matrix.val = 1) :
    matrix.inv = matrix.val.transpose := by
  calc
    matrix.inv = (matrix.val.transpose * matrix.val) * matrix.inv := by rw [orthogonal, one_mul]
    _ = matrix.val.transpose := by rw [mul_assoc, matrix.val_inv, mul_one]

theorem realOrthogonal_isClosed :
    IsClosed {matrix : RealGL3 | matrix.val.transpose * matrix.val = 1} := by
  have values : Continuous (Units.val : RealGL3 → Matrix (Fin 3) (Fin 3) ℝ) := Units.continuous_val
  exact isClosed_eq (values.matrix_transpose.mul values) continuous_const

theorem realOrthogonal_isCompact :
    IsCompact {matrix : RealGL3 | matrix.val.transpose * matrix.val = 1} := by
  let ball : Set (Matrix (Fin 3) (Fin 3) ℝ) := Metric.closedBall 0 1
  have ball_compact : IsCompact ball := isCompact_closedBall _ _
  have container_compact :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 3) (Fin 3) ℝ)).isCompact_preimage
      (ball_compact.prod (ball_compact.image MulOpposite.continuous_op))
  apply container_compact.of_isClosed_subset realOrthogonal_isClosed
  intro matrix orthogonal
  have value_bound : ‖matrix.val‖ ≤ 1 := (Matrix.norm_le_iff (by norm_num)).mpr
    (real_orthogonal_entry_bound orthogonal)
  have inverse_bound : ‖matrix.inv‖ ≤ 1 := by
    apply (Matrix.norm_le_iff (by norm_num)).mpr
    intro row column
    rw [real_orthogonal_inverse orthogonal]
    exact real_orthogonal_entry_bound orthogonal column row
  change matrix.val ∈ ball ∧ MulOpposite.op matrix.inv ∈ MulOpposite.op '' ball
  exact ⟨by simpa [ball, Metric.mem_closedBall, dist_zero_right] using value_bound,
    ⟨matrix.inv, by simpa [ball, Metric.mem_closedBall, dist_zero_right] using inverse_bound, rfl⟩⟩

theorem pairMatrix_continuous {X : Type*} [TopologicalSpace X]
    {realMatrices : X → Matrix (Fin 3) (Fin 3) ℝ}
    {finiteMatrices : X → Matrix (Fin 3) (Fin 3) FiniteAdeles}
    (real_continuous : Continuous realMatrices) (finite_continuous : Continuous finiteMatrices) :
    Continuous (fun input => pairMatrix (realMatrices input) (finiteMatrices input)) := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact ((continuous_apply column).comp ((continuous_apply row).comp real_continuous)).prodMk
    ((continuous_apply column).comp ((continuous_apply row).comp finite_continuous))

theorem combineGL_continuous : Continuous (fun input : RealGL3 × FiniteGL => combineGL input.1 input.2) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply pairMatrix_continuous
    · exact Units.continuous_val.comp continuous_fst
    · exact Units.continuous_val.comp continuous_snd
  · apply pairMatrix_continuous
    · exact Units.continuous_val.comp continuous_fst.inv
    · exact Units.continuous_val.comp continuous_snd.inv

theorem realGroup_combineGL (realMatrix : RealGL3) (finiteMatrix : FiniteGL) :
    realGroup (combineGL realMatrix finiteMatrix) = realMatrix := by
  apply Units.ext
  rfl

theorem finiteGroup_combineGL (realMatrix : RealGL3) (finiteMatrix : FiniteGL) :
    finiteGroup (combineGL realMatrix finiteMatrix) = finiteMatrix := by
  apply Units.ext
  rfl

theorem integralGL_compactSpace : CompactSpace (GL3 IntegralAdeles) := by
  let : ContinuousMul IntegralAdeles :=
    integralEmbedding_isOpenEmbedding.isEmbedding.isInducing.continuousMul integralEmbedding
  let : ContinuousAdd IntegralAdeles :=
    integralEmbedding_isOpenEmbedding.isEmbedding.isInducing.continuousAdd integralEmbedding
  let : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  let : ContinuousMul (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    ⟨continuous_fst.matrix_mul continuous_snd⟩
  infer_instance

theorem finiteIntegralGL_isCompact :
    IsCompact (Set.range (GeneralLinearGroup.map (n := Fin 3) integralEmbedding)) := by
  let : CompactSpace (GL3 IntegralAdeles) := integralGL_compactSpace
  exact isCompact_range
    (generalLinearGroup_map_continuous integralEmbedding integralEmbedding_isOpenEmbedding.continuous 3)

theorem finiteLevel_isCompact : IsCompact (finiteLevel : Set FiniteGL) := by
  apply finiteIntegralGL_isCompact.of_isClosed_subset (finiteLevel.isClosed_of_isOpen finiteLevel_isOpen)
  intro matrix member
  obtain ⟨integralMatrix, _, represents⟩ := member
  exact ⟨integralMatrix, represents⟩

def maximalCompactGroup : Subgroup AdelicGL where
  carrier := {matrix | inMaximalCompact matrix}
  one_mem' := ⟨by simp, ⟨1, by simp⟩⟩
  mul_mem' {first second} first_member second_member := by
    constructor
    · rw [map_mul]
      exact real_orthogonal_mul first_member.1 second_member.1
    · exact finite_integral_mul first_member.2 second_member.2
  inv_mem' {matrix} member := by
    constructor
    · rw [map_inv]
      exact real_orthogonal_inv member.1
    · obtain ⟨integralMatrix, represents⟩ := member.2
      exact ⟨integralMatrix⁻¹, by rw [map_inv, represents, map_inv]⟩

theorem maximalCompact_isCompact : IsCompact {matrix : AdelicGL | inMaximalCompact matrix} := by
  let : CompactSpace (GL3 IntegralAdeles) := integralGL_compactSpace
  have parametrization_continuous : Continuous (fun input : RealGL3 × GL3 IntegralAdeles =>
      combineGL input.1 (GeneralLinearGroup.map integralEmbedding input.2)) :=
    combineGL_continuous.comp (continuous_fst.prodMk
      ((generalLinearGroup_map_continuous integralEmbedding integralEmbedding_isOpenEmbedding.continuous 3).comp
        continuous_snd))
  have image_compact := (realOrthogonal_isCompact.prod
    (isCompact_univ : IsCompact (Set.univ : Set (GL3 IntegralAdeles)))).image parametrization_continuous
  have image_eq : (fun input : RealGL3 × GL3 IntegralAdeles =>
      combineGL input.1 (GeneralLinearGroup.map integralEmbedding input.2)) ''
      ({matrix : RealGL3 | matrix.val.transpose * matrix.val = 1} ×ˢ Set.univ) =
        {matrix : AdelicGL | inMaximalCompact matrix} := by
    ext matrix
    constructor
    · rintro ⟨⟨realMatrix, integralMatrix⟩, ⟨orthogonal, _⟩, rfl⟩
      exact ⟨by simpa only [realGroup_combineGL] using
          (show realMatrix.val.transpose * realMatrix.val = 1 from orthogonal),
        ⟨integralMatrix, (finiteGroup_combineGL _ _).symm⟩⟩
    · rintro ⟨orthogonal, integralMatrix, finite_eq⟩
      refine ⟨(realGroup matrix, integralMatrix), ⟨orthogonal, Set.mem_univ _⟩, ?_⟩
      change combineGL (realGroup matrix) (GeneralLinearGroup.map integralEmbedding integralMatrix) = matrix
      rw [finite_eq]
      apply Units.ext
      rfl
  rwa [image_eq] at image_compact

theorem maximalCompactGroup_compactSpace : CompactSpace maximalCompactGroup :=
  isCompact_iff_compactSpace.mp maximalCompact_isCompact

theorem flat_section_maximalCompact_bound
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter compactMatrix,
      inMaximalCompact compactMatrix → ‖family parameter compactMatrix‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := maximalCompact_isCompact.exists_bound_of_continuousOn
    (induced_continuous (flat.1 cohomologicalPoint)).continuousOn
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro parameter compactMatrix compact_spec
  have scaling := flat_section_compact_levi_scaling flat parameter 1 compactMatrix compact_spec
  have levi_one : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
  simp only [levi_one, one_mul, map_one, normPower_one] at scaling
  rw [scaling]
  exact (bounded compactMatrix compact_spec).trans (le_max_right _ _)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
