module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearUnipotent

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def realSpecialDiagonalBox (lower upper : ℝ) : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  Subtype.val ⁻¹' (Matrix.diagonal '' {entries : Fin 3 → ℝ | ∀ index, entries index ∈ Set.Icc lower upper})

theorem realSpecialDiagonalBox_isCompact (lower upper : ℝ) :
    IsCompact (realSpecialDiagonalBox lower upper) := by
  apply SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage
  exact (isCompact_pi_infinite (fun _ : Fin 3 => isCompact_Icc)).image continuous_id.matrix_diagonal

theorem realSpecialDiagonalBox_positive {lower upper : ℝ} (positive : 0 < lower)
    {matrix : SpecialLinearGroup (Fin 3) ℝ} (member : matrix ∈ realSpecialDiagonalBox lower upper) :
    realPositiveDiagonal (SpecialLinearGroup.toGL matrix) := by
  obtain ⟨entries, bounds, represents⟩ := member
  constructor
  · intro row column different
    change matrix.val row column = 0
    rw [← represents]
    exact Matrix.diagonal_apply_ne _ different
  · intro index
    change 0 < matrix.val index index
    rw [← represents, Matrix.diagonal_apply_eq]
    exact positive.trans_le (bounds index).1

def realSpecialUnipotentBox (r s t : ℝ) : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  (fun coordinates : ℝ × ℝ × ℝ =>
    realSpecialUnipotent coordinates.1 coordinates.2.1 coordinates.2.2) ''
      (Set.Icc (-r) r ×ˢ (Set.Icc (-s) s ×ˢ Set.Icc (-t) t))

theorem realSpecialUnipotentBox_isCompact (r s t : ℝ) :
    IsCompact (realSpecialUnipotentBox r s t) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image realSpecialUnipotent_continuous

theorem mem_realSpecialUnipotentBox_iff {matrix : SpecialLinearGroup (Fin 3) ℝ} {r s t : ℝ} :
    matrix ∈ realSpecialUnipotentBox r s t ↔
      ∃ x y z, |x| ≤ r ∧ |y| ≤ s ∧ |z| ≤ t ∧ matrix = realSpecialUnipotent x y z := by
  constructor
  · rintro ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩
    exact ⟨x, y, z, abs_le.mpr hx, abs_le.mpr hy, abs_le.mpr hz, rfl⟩
  · rintro ⟨x, y, z, hx, hy, hz, rfl⟩
    exact ⟨(x, y, z), ⟨abs_le.mp hx, abs_le.mp hy, abs_le.mp hz⟩, rfl⟩

def realSpecialSiegelBox (r s t : ℝ) (diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)) :
    Set (SpecialLinearGroup (Fin 3) ℝ) :=
  realSpecialUnipotentBox r s t * diagonals * realSpecialOrthogonal

theorem realSpecialSiegelBox_isCompact (r s t : ℝ)
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact diagonals) :
    IsCompact (realSpecialSiegelBox r s t diagonals) :=
  ((realSpecialUnipotentBox_isCompact r s t).mul compact).mul realSpecialOrthogonal_isCompact

theorem mem_realSpecialSiegelBox_iff {matrix : SpecialLinearGroup (Fin 3) ℝ} {r s t : ℝ}
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} :
    matrix ∈ realSpecialSiegelBox r s t diagonals ↔
      ∃ x y z diagonal rotation, |x| ≤ r ∧ |y| ≤ s ∧ |z| ≤ t ∧
        diagonal ∈ diagonals ∧ rotation ∈ realSpecialOrthogonal ∧
        matrix = realSpecialUnipotent x y z * diagonal * rotation := by
  constructor
  · rintro ⟨_, ⟨unipotent, hu, diagonal, hd, rfl⟩, rotation, hk, rfl⟩
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mem_realSpecialUnipotentBox_iff.mp hu
    exact ⟨x, y, z, diagonal, rotation, hx, hy, hz, hd, hk, rfl⟩
  · rintro ⟨x, y, z, diagonal, rotation, hx, hy, hz, hd, hk, rfl⟩
    exact ⟨_, ⟨_, mem_realSpecialUnipotentBox_iff.mpr ⟨x, y, z, hx, hy, hz, rfl⟩,
      diagonal, hd, rfl⟩, rotation, hk, rfl⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
