module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.QuotientPieces
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CountableCoverDomination
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section


open Matrix MeasureTheory Filter
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)
local notation "PieceIndex" => integerSpecialLinearReduction.range × ℕ × ℕ

theorem ennreal_double_geometric_finite {ratio bound : ℝ≥0∞} (small : ratio < 1) (finite : bound < ⊤) :
    (∑' m : ℕ, ∑' n : ℕ, ratio ^ (m + n) * bound) < ⊤ := by
  simp only [pow_add, mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have geometric_finite : (1 - ratio)⁻¹ < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr small)))
  exact ENNReal.mul_lt_top geometric_finite (ENNReal.mul_lt_top geometric_finite finite)

theorem principalQuotientPieces_weighted_volume :
    (∑' index : PieceIndex, (16 : ℝ≥0∞) ^ (index.2.1 + index.2.2) *
      principalSpecialLinearQuotientMeasure (principalQuotientPiece index.1 index.2.1 index.2.2)) < ⊤ := by
  let : Fintype integerSpecialLinearReduction.range := Fintype.ofFinite _
  rw [ENNReal.tsum_prod', tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro residue _
  rw [ENNReal.tsum_prod']
  let bound := realSpecialLinearHaar (realSpecialSiegelBox 4 4 4 (realSpecialDiagonalBox (1 / 64) 64))
  have bound_finite : bound < ⊤ :=
    (realSpecialSiegelBox_isCompact 4 4 4 (realSpecialDiagonalBox_isCompact (1 / 64) 64)).measure_lt_top
  have ratio_small : (16 : ℝ≥0∞) * 64⁻¹ < 1 := by
    change (16 : ℝ≥0∞) / 64 < 1
    apply (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
    norm_num
  apply lt_of_le_of_lt _ (ennreal_double_geometric_finite ratio_small bound_finite)
  apply ENNReal.tsum_le_tsum
  intro m
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ (16 : ℝ≥0∞) ^ (m + n) * ((64 : ℝ≥0∞)⁻¹ ^ (m + n) * bound) :=
      mul_le_mul' le_rfl (principalQuotientPiece_measure_le residue m n)
    _ = _ := by rw [← mul_assoc, ← mul_pow]

theorem principalQuotientPieces_scaled_weighted_volume (coefficient : ℝ) :
    (∑' index : PieceIndex, (ENNReal.ofReal coefficient * (16 : ℝ≥0∞) ^ (index.2.1 + index.2.2)) *
      principalSpecialLinearQuotientMeasure (principalQuotientPiece index.1 index.2.1 index.2.2)) < ⊤ := by
  simp only [mul_assoc, ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top (by finiteness) principalQuotientPieces_weighted_volume

theorem principalQuotientPieces_index_cover :
    (⋃ index : PieceIndex, principalQuotientPiece index.1 index.2.1 index.2.2) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro point
  have covered : point ∈ ⋃ residue : integerSpecialLinearReduction.range, ⋃ m : ℕ, ⋃ n : ℕ,
      principalQuotientPiece residue m n := by rw [principalQuotientPieces_cover]; trivial
  obtain ⟨residue, covered⟩ := Set.mem_iUnion.mp covered
  obtain ⟨m, covered⟩ := Set.mem_iUnion.mp covered
  obtain ⟨n, covered⟩ := Set.mem_iUnion.mp covered
  exact Set.mem_iUnion.mpr ⟨(residue, m, n), covered⟩

theorem principalQuotient_tendsto_integral_of_piece_bounds {T E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (filter : Filter T) [filter.IsCountablyGenerated]
    (coefficient : ℝ) {family : T → PrincipalQuotient → E} {limit : PrincipalQuotient → E}
    (measurable : ∀ᶠ parameter in filter, AEStronglyMeasurable (family parameter) principalSpecialLinearQuotientMeasure)
    (bounded : ∀ᶠ parameter in filter, ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n,
        ENNReal.ofReal ‖family parameter point‖ ≤ ENNReal.ofReal coefficient * (16 : ℝ≥0∞) ^ (m + n))
    (converges : ∀ᵐ point ∂principalSpecialLinearQuotientMeasure,
      Tendsto (fun parameter => family parameter point) filter (nhds (limit point))) :
    Tendsto (fun parameter => ∫ point, family parameter point ∂principalSpecialLinearQuotientMeasure)
      filter (nhds (∫ point, limit point ∂principalSpecialLinearQuotientMeasure)) := by
  apply tendsto_integral_of_countable_cover
    (fun index : PieceIndex => principalQuotientPiece index.1 index.2.1 index.2.2)
    (fun index : PieceIndex => ENNReal.ofReal coefficient * (16 : ℝ≥0∞) ^ (index.2.1 + index.2.2))
    principalSpecialLinearQuotientMeasure filter
    (fun index => principalQuotientPiece_measurable index.1 index.2.1 index.2.2)
    principalQuotientPieces_index_cover (principalQuotientPieces_scaled_weighted_volume coefficient) measurable
  · filter_upwards [bounded] with parameter bound
    rintro ⟨residue, m, n⟩
    exact bound residue m n
  · exact converges

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
