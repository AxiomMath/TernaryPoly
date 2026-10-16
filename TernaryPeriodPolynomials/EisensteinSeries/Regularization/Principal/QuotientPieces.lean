module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.QuotientImageMeasure
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.QuotientMeasure

@[expose] public section


open Matrix MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

noncomputable def principalReducedPiece (residue : integerSpecialLinearReduction.range) (m n : ℕ) : Set RealSL3 :=
  (SpecialLinearGroup.map (Int.castRingHom ℝ) (integerSpecialLinearReductionRepresentative residue))⁻¹ •
    (realSpecialScaling m n • realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64))

theorem principalReducedPiece_isCompact (residue : integerSpecialLinearReduction.range) (m n : ℕ) :
    IsCompact (principalReducedPiece residue m n) :=
  ((realSpecialShrinkingBox_isCompact m n (realSpecialDiagonalBox_isCompact (1 / 64) 64)).smul
    (realSpecialScaling m n)).smul _

noncomputable def principalQuotientPiece (residue : integerSpecialLinearReduction.range) (m n : ℕ) :
    Set PrincipalQuotient :=
  (Quotient.mk (MulAction.orbitRel principalRealSpecialLinear RealSL3)) '' principalReducedPiece residue m n

theorem principalQuotientPiece_measurable (residue : integerSpecialLinearReduction.range) (m n : ℕ) :
    MeasurableSet (principalQuotientPiece residue m n) :=
  orbit_quotient_image_measurable (principalReducedPiece_isCompact residue m n).measurableSet

theorem principalQuotientPiece_measure_le (residue : integerSpecialLinearReduction.range) (m n : ℕ) :
    principalSpecialLinearQuotientMeasure (principalQuotientPiece residue m n) ≤
      (64 : ℝ≥0∞)⁻¹ ^ (m + n) *
        realSpecialLinearHaar (realSpecialSiegelBox 4 4 4 (realSpecialDiagonalBox (1 / 64) 64)) := by
  have bound := orbit_quotient_image_measure_le principalRealSpecialLinearDomain_fundamental
    (principalReducedPiece_isCompact residue m n).measurableSet
  change principalSpecialLinearQuotientMeasure (principalQuotientPiece residue m n) ≤
    realSpecialLinearHaar (principalReducedPiece residue m n) at bound
  rw [principalReducedPiece, measure_smul, measure_smul] at bound
  exact bound.trans (realSpecialShrinkingBox_volume_bound m n (realSpecialDiagonalBox_isCompact (1 / 64) 64)
    (fun _ member => realSpecialDiagonalBox_positive (by norm_num) member))

theorem principalQuotientPieces_cover :
    (⋃ residue : integerSpecialLinearReduction.range, ⋃ m : ℕ, ⋃ n : ℕ,
      principalQuotientPiece residue m n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro point
  induction point using Quotient.inductionOn with
  | h matrix =>
    obtain ⟨principal, member⟩ := principalRealSpecialLinearCover_orbit matrix
    obtain ⟨residue, reduced, reduced_member, equality⟩ := Set.mem_iUnion.mp member
    obtain ⟨m, m_member⟩ := Set.mem_iUnion.mp (realSpecialLinearReducedCover_subset_shrinking reduced_member)
    obtain ⟨n, n_member⟩ := Set.mem_iUnion.mp m_member
    apply Set.mem_iUnion.mpr
    refine ⟨residue, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨n, ?_⟩⟩⟩
    refine ⟨principal • matrix, ⟨reduced, n_member, equality⟩, ?_⟩
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨principal, rfl⟩)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
