module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.OrbitalMass

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealOrbitalMass
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GramCutoff

def gram (value : Rectangular ℝ) : BinaryMatrix := value.transpose * value

theorem gram_contDiff : ContDiff ℝ ⊤ gram := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem gram_diagonal (value : Rectangular ℝ) (column : Fin 2) :
    gram value column column = ∑ row : Fin 3, (value row column) ^ 2 := by
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem gram_det (value : Rectangular ℝ) : (gram value).det = ∑ row : Fin 3, (exterior value row) ^ 2 := by
  simp [gram, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_three, exterior, crossProduct]
  ring

theorem gram_det_nonzero (value : Rectangular ℝ) (nonzero : (gram value).det ≠ 0) : FullRank value := by
  intro vanishing
  apply nonzero
  rw [gram_det, vanishing]
  simp

theorem gram_orthogonal (orthogonal : RealGL3) (orthogonality : orthogonal.val.transpose * orthogonal.val = 1)
    (value : Rectangular ℝ) : gram (orthogonal.val * value) = gram value := by
  rw [gram, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc orthogonal.val.transpose,
    orthogonality, Matrix.one_mul]
  rfl

theorem gram_standard : gram (columns (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [gram, columns, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem support_preimage (function : BinaryMatrix → ℝ) :
    tsupport (function ∘ gram) ⊆ gram ⁻¹' tsupport function := by
  apply closure_minimal
  · intro value nonzero
    exact subset_closure nonzero
  · exact isClosed_closure.preimage gram_contDiff.continuous

theorem compactSupport (function : BinaryMatrix → ℝ) (compact : HasCompactSupport function) :
    HasCompactSupport (function ∘ gram) := by
  obtain ⟨bound, bounded⟩ := isBounded_iff_forall_norm_le.mp compact.isBounded
  let radius : ℝ := max bound 0 + 1
  have radiusNonnegative : 0 ≤ radius := by dsimp [radius]; positivity
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Rectangular ℝ) radius)
  intro value nonzero
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (Matrix.norm_le_iff radiusNonnegative).mpr
  intro row column
  have gramBound : ‖gram value‖ ≤ bound := bounded _ (subset_closure nonzero)
  have diagonalBound : ‖gram value column column‖ ≤ ‖gram value‖ :=
    (Matrix.norm_le_iff (norm_nonneg (gram value))).mp le_rfl column column
  have squareBound : (value row column) ^ 2 ≤ gram value column column := by
    rw [gram_diagonal]
    exact Finset.single_le_sum (fun index _ => sq_nonneg (value index column)) (Finset.mem_univ row)
  have absoluteBound : gram value column column ≤ ‖gram value column column‖ := Real.le_norm_self _
  rw [Real.norm_eq_abs]
  dsimp [radius]
  nlinarith [le_max_left bound 0, le_max_right bound 0, sq_nonneg (|value row column| - 1),
    sq_abs (value row column)]

theorem exists_cutoff :
    ∃ cutoff : Rectangular ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value} ∧
      Set.range cutoff ⊆ Set.Icc 0 1 ∧ cutoff (columns (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 ∧
      ∀ orthogonal : RealGL3, orthogonal.val.transpose * orthogonal.val = 1 →
        ∀ value : Rectangular ℝ, cutoff (orthogonal.val * value) = cutoff value := by
  have determinant : Continuous (fun matrix : BinaryMatrix => matrix.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have neighborhood : {matrix : BinaryMatrix | matrix.det ≠ 0} ∈ nhds (1 : BinaryMatrix) :=
    (isOpen_ne_fun determinant continuous_const).mem_nhds (by simp)
  obtain ⟨function, supported, compact, smooth, range, value⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) neighborhood
  refine ⟨function ∘ gram, smooth.comp (gram_contDiff.of_le le_top), compactSupport function compact,
    ?_, ?_, ?_, ?_⟩
  · intro frame membership
    exact gram_det_nonzero frame (supported (support_preimage function membership))
  · rintro _ ⟨frame, rfl⟩
    exact range ⟨gram frame, rfl⟩
  · dsimp only [Function.comp_apply]
    rw [gram_standard, value]
  · intro orthogonal orthogonality frame
    dsimp only [Function.comp_apply]
    rw [gram_orthogonal orthogonal orthogonality]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GramCutoff
