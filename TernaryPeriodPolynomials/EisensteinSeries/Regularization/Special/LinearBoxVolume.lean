module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.UnipotentGridPacking
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.OrbitCoverMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem finite_disjoint_translate_measure_bound
    {G X I : Type*} [Group G] [MulAction G X] [Fintype I] [MeasurableSpace X]
    [MeasurableConstSMul G X] {measure : Measure X} [SMulInvariantMeasure G X measure]
    {piece container : Set X} (measurable : MeasurableSet piece) (shift : I → G)
    (disjoint : Pairwise (fun i j => Disjoint (shift i • piece) (shift j • piece)))
    (contained : ∀ i, shift i • piece ⊆ container) :
    (Fintype.card I : ℝ≥0∞) * measure piece ≤ measure container := by
  calc
    (Fintype.card I : ℝ≥0∞) * measure piece = ∑' i, measure (shift i • piece) := by
      simp [measure_smul, tsum_fintype, nsmul_eq_mul]
    _ = measure (⋃ i, shift i • piece) :=
      (measure_iUnion disjoint (fun i => measurable.const_smul (shift i))).symm
    _ ≤ measure container := measure_mono (Set.iUnion_subset contained)

theorem realSpecialSiegelBox_volume_bound {L M N : ℕ} {r s t : ℝ}
    (rpos : 0 < r) (spos : 0 < s) (tpos : 0 < t)
    (rsmall : r ≤ 1 / 2) (ssmall : s ≤ 1 / 2) (tsmall : t ≤ 1 / 2)
    (rbound : r * L ≤ 1 / 2) (sbound : s * M ≤ 1 / 2) (tbound : t * N ≤ 1 / 2)
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact diagonals)
    (positive : ∀ diagonal ∈ diagonals, realPositiveDiagonal (SpecialLinearGroup.toGL diagonal)) :
    ((L * (M * N) : ℕ) : ℝ≥0∞) * realSpecialLinearHaar (realSpecialSiegelBox r s t diagonals) ≤
      realSpecialLinearHaar (realSpecialSiegelBox 4 4 4 diagonals) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    finite_disjoint_translate_measure_bound
      (measure := realSpecialLinearHaar) (realSpecialSiegelBox_isCompact r s t compact).measurableSet
      (realSpecialGridShift (L := L) (M := M) (N := N) r s t)
      (realSpecialSiegelBox_grid_disjoint rpos spos tpos positive)
      (realSpecialSiegelBox_grid_subset rpos.le spos.le tpos.le rsmall ssmall tsmall rbound sbound tbound diagonals)

noncomputable def realSpecialBoxRadius (index : ℕ) : ℝ := (8 : ℝ)⁻¹ ^ index / 2

theorem realSpecialBoxRadius_positive (index : ℕ) : 0 < realSpecialBoxRadius index := by
  unfold realSpecialBoxRadius
  positivity

theorem realSpecialBoxRadius_le_half (index : ℕ) : realSpecialBoxRadius index ≤ 1 / 2 := by
  unfold realSpecialBoxRadius
  exact div_le_div_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)

theorem realSpecialBoxRadius_mul (index : ℕ) : realSpecialBoxRadius index * (8 ^ index : ℕ) = 1 / 2 := by
  unfold realSpecialBoxRadius
  push_cast
  rw [div_mul_eq_mul_div, ← mul_pow]
  norm_num

def realSpecialShrinkingBox (m n : ℕ) (diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)) :
    Set (SpecialLinearGroup (Fin 3) ℝ) :=
  realSpecialSiegelBox (realSpecialBoxRadius m) (realSpecialBoxRadius n) (realSpecialBoxRadius (m + n)) diagonals

theorem realSpecialShrinkingBox_isCompact (m n : ℕ)
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact diagonals) :
    IsCompact (realSpecialShrinkingBox m n diagonals) := realSpecialSiegelBox_isCompact _ _ _ compact

theorem realSpecialShrinkingBox_volume_bound (m n : ℕ)
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact diagonals)
    (positive : ∀ diagonal ∈ diagonals, realPositiveDiagonal (SpecialLinearGroup.toGL diagonal)) :
    realSpecialLinearHaar (realSpecialShrinkingBox m n diagonals) ≤
      (64 : ℝ≥0∞)⁻¹ ^ (m + n) * realSpecialLinearHaar (realSpecialSiegelBox 4 4 4 diagonals) := by
  have packing := realSpecialSiegelBox_volume_bound
    (L := 8 ^ m) (M := 8 ^ n) (N := 8 ^ (m + n))
    (realSpecialBoxRadius_positive m) (realSpecialBoxRadius_positive n) (realSpecialBoxRadius_positive (m + n))
    (realSpecialBoxRadius_le_half m) (realSpecialBoxRadius_le_half n) (realSpecialBoxRadius_le_half (m + n))
    (realSpecialBoxRadius_mul m).le (realSpecialBoxRadius_mul n).le (realSpecialBoxRadius_mul (m + n)).le compact positive
  have count : 8 ^ m * (8 ^ n * 8 ^ (m + n)) = (64 : ℕ) ^ (m + n) := by
    rw [← mul_assoc, ← pow_add, ← mul_pow]
    norm_num
  rw [count, Nat.cast_pow, Nat.cast_ofNat] at packing
  have bound := (ENNReal.mul_le_iff_le_inv (by positivity : (64 : ℝ≥0∞) ^ (m + n) ≠ 0)
    (by finiteness : (64 : ℝ≥0∞) ^ (m + n) ≠ ⊤)).mp packing
  simpa only [ENNReal.inv_pow, realSpecialShrinkingBox] using bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
