module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.Decomposition
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact

theorem orthogonal_entry_bound (matrix : Matrix (Fin 3) (Fin 3) ℝ)
    (orthogonality : matrix.transpose * matrix = 1) (row column : Fin 3) :
    ‖matrix row column‖ ≤ 1 := by
  have columnNorm := congrArg
    (fun product : Matrix (Fin 3) (Fin 3) ℝ => product column column) orthogonality
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    Matrix.one_apply_eq] at columnNorm
  have squareBound : (matrix row column) ^ 2 ≤ 1 := by
    fin_cases row <;> dsimp <;>
      nlinarith [sq_nonneg (matrix 0 column), sq_nonneg (matrix 1 column),
        sq_nonneg (matrix 2 column)]
  exact (sq_le_one_iff_abs_le_one _).mp squareBound

theorem isCompact_orthogonal_matrices :
    IsCompact {matrix : Matrix (Fin 3) (Fin 3) ℝ | matrix.transpose * matrix = 1} := by
  have transposeContinuous : Continuous
      (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix.transpose) :=
    continuous_pi (fun row => continuous_pi (fun column =>
      (continuous_apply row).comp (continuous_apply column)))
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (transposeContinuous.mul continuous_id) continuous_const
  · apply (Metric.isBounded_closedBall (x := (0 : Matrix (Fin 3) (Fin 3) ℝ))
      (r := 1)).subset
    intro matrix orthogonality
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Matrix.norm_le_iff (by norm_num)).mpr (orthogonal_entry_bound matrix orthogonality)

noncomputable def orthogonalUnit
    (matrix : {matrix : Matrix (Fin 3) (Fin 3) ℝ | matrix.transpose * matrix = 1}) :
    RealGL3 :=
  ⟨matrix.val, matrix.val.transpose,
    (Matrix.mem_orthogonalGroup_iff _ _).mp
      ((Matrix.mem_orthogonalGroup_iff' _ _).mpr matrix.property), matrix.property⟩

theorem orthogonalUnit_continuous : Continuous orthogonalUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · change Continuous (fun matrix :
        {matrix : Matrix (Fin 3) (Fin 3) ℝ | matrix.transpose * matrix = 1} =>
      matrix.val.transpose)
    exact continuous_pi (fun row => continuous_pi (fun column =>
      (continuous_apply row).comp ((continuous_apply column).comp continuous_subtype_val)))

theorem isCompact_orthogonal :
    IsCompact {realMatrix : RealGL3 | realMatrix.val.transpose * realMatrix.val = 1} := by
  have compactSubtype : CompactSpace
      {matrix : Matrix (Fin 3) (Fin 3) ℝ | matrix.transpose * matrix = 1} :=
    isCompact_iff_compactSpace.mp isCompact_orthogonal_matrices
  have compactRange := isCompact_range orthogonalUnit_continuous
  have rangeEquality : Set.range orthogonalUnit =
      {realMatrix : RealGL3 | realMatrix.val.transpose * realMatrix.val = 1} := by
    ext realMatrix
    constructor
    · rintro ⟨matrix, rfl⟩
      exact matrix.property
    · intro orthogonality
      refine ⟨⟨realMatrix.val, orthogonality⟩, ?_⟩
      exact Units.ext rfl
  rwa [rangeEquality] at compactRange

theorem planeCuspVector_bound_on_orthogonal {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 →
      ‖(TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection
        (basePoint * atInfinity realMatrix)).val‖ ≤ bound := by
  obtain ⟨bound, boundProperty⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Smooth.planeCuspVector_bound_on_compact inducedSection basePoint
      isCompact_orthogonal
  refine ⟨bound, ?_, boundProperty⟩
  exact (norm_nonneg _).trans (boundProperty 1 (by simp))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact
