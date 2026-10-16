module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.CoverDomination

@[expose] public section


open Matrix MeasureTheory Filter
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)
local notation "PieceIndex" => integerSpecialLinearReduction.range × ℕ × ℕ

theorem principalQuotientPieces_geometric_weighted_volume {base : ℝ≥0∞} (small : base < 64) :
    (∑' index : PieceIndex, base ^ (index.2.1 + index.2.2) *
      principalSpecialLinearQuotientMeasure (principalQuotientPiece index.1 index.2.1 index.2.2)) < ⊤ := by
  let : Fintype integerSpecialLinearReduction.range := Fintype.ofFinite _
  rw [ENNReal.tsum_prod', tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro residue _
  rw [ENNReal.tsum_prod']
  let bound := realSpecialLinearHaar (realSpecialSiegelBox 4 4 4 (realSpecialDiagonalBox (1 / 64) 64))
  have bound_finite : bound < ⊤ :=
    (realSpecialSiegelBox_isCompact 4 4 4 (realSpecialDiagonalBox_isCompact (1 / 64) 64)).measure_lt_top
  have ratio_small : base * 64⁻¹ < 1 := by
    change base / 64 < 1
    apply (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
    simpa only [one_mul] using small
  apply lt_of_le_of_lt _ (ennreal_double_geometric_finite ratio_small bound_finite)
  apply ENNReal.tsum_le_tsum
  intro m
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ base ^ (m + n) * ((64 : ℝ≥0∞)⁻¹ ^ (m + n) * bound) :=
      mul_le_mul' le_rfl (principalQuotientPiece_measure_le residue m n)
    _ = _ := by rw [← mul_assoc, ← mul_pow]

theorem principalQuotient_tendsto_integral_of_geometric_bounds {T E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (filter : Filter T) [filter.IsCountablyGenerated]
    (coefficient : ℝ) {base : ℝ≥0∞} (small : base < 64)
    {family : T → PrincipalQuotient → E} {limit : PrincipalQuotient → E}
    (measurable : ∀ᶠ parameter in filter, AEStronglyMeasurable (family parameter) principalSpecialLinearQuotientMeasure)
    (bounded : ∀ᶠ parameter in filter, ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n,
        ENNReal.ofReal ‖family parameter point‖ ≤ ENNReal.ofReal coefficient * base ^ (m + n))
    (converges : ∀ᵐ point ∂principalSpecialLinearQuotientMeasure,
      Tendsto (fun parameter => family parameter point) filter (nhds (limit point))) :
    Tendsto (fun parameter => ∫ point, family parameter point ∂principalSpecialLinearQuotientMeasure)
      filter (nhds (∫ point, limit point ∂principalSpecialLinearQuotientMeasure)) := by
  have weighted_finite : (∑' index : PieceIndex,
      (ENNReal.ofReal coefficient * base ^ (index.2.1 + index.2.2)) *
        principalSpecialLinearQuotientMeasure (principalQuotientPiece index.1 index.2.1 index.2.2)) < ⊤ := by
    simp only [mul_assoc, ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (by finiteness) (principalQuotientPieces_geometric_weighted_volume small)
  apply tendsto_integral_of_countable_cover
    (fun index : PieceIndex => principalQuotientPiece index.1 index.2.1 index.2.2)
    (fun index : PieceIndex => ENNReal.ofReal coefficient * base ^ (index.2.1 + index.2.2))
    principalSpecialLinearQuotientMeasure filter
    (fun index => principalQuotientPiece_measurable index.1 index.2.1 index.2.2)
    principalQuotientPieces_index_cover weighted_finite measurable
  · filter_upwards [bounded] with parameter bound
    rintro ⟨residue, m, n⟩
    exact bound residue m n
  · exact converges

theorem principalQuotient_integrable_of_geometric_bounds {E : Type*} [NormedAddCommGroup E]
    (coefficient : ℝ) {base : ℝ≥0∞} (small : base < 64) {function : PrincipalQuotient → E}
    (measurable : AEStronglyMeasurable function principalSpecialLinearQuotientMeasure)
    (bounded : ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n,
        ENNReal.ofReal ‖function point‖ ≤ ENNReal.ofReal coefficient * base ^ (m + n)) :
    Integrable function principalSpecialLinearQuotientMeasure := by
  have weighted_finite : (∑' index : PieceIndex,
      (ENNReal.ofReal coefficient * base ^ (index.2.1 + index.2.2)) *
        principalSpecialLinearQuotientMeasure (principalQuotientPiece index.1 index.2.1 index.2.2)) < ⊤ := by
    simp only [mul_assoc, ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (by finiteness) (principalQuotientPieces_geometric_weighted_volume small)
  apply (weightedCoverMajorant_integrable
    (fun index : PieceIndex => principalQuotientPiece index.1 index.2.1 index.2.2)
    (fun index : PieceIndex => ENNReal.ofReal coefficient * base ^ (index.2.1 + index.2.2))
    principalSpecialLinearQuotientMeasure
    (fun index => principalQuotientPiece_measurable index.1 index.2.1 index.2.2) weighted_finite).mono' measurable
  apply weightedCoverMajorant_dominates
    (fun index : PieceIndex => principalQuotientPiece index.1 index.2.1 index.2.2)
    (fun index : PieceIndex => ENNReal.ofReal coefficient * base ^ (index.2.1 + index.2.2))
    principalSpecialLinearQuotientMeasure
    (fun index => principalQuotientPiece_measurable index.1 index.2.1 index.2.2)
    principalQuotientPieces_index_cover weighted_finite
  rintro ⟨residue, m, n⟩
  exact bounded residue m n

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
