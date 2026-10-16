module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportClosedExact

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- Compatible local classes on two closed supports always have an actual class on their union. -/
theorem closed_compatible_iff_glues (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ)
    (z : (supportHomology A k ⊞ supportHomology B k : ModuleCat ℚ)) :
    closedDifference A B k z = 0 ↔ ∃ x, closedPair A B k x = z := by
  change z ∈ LinearMap.ker (closedDifference A B k).hom ↔ z ∈ LinearMap.range (closedPair A B k).hom
  rw [closed_exact_pair A B hA hB k]

/-- The precise obstruction to unique closed-support gluing is the preceding boundary image. -/
theorem closed_injective_iff_connecting_zero (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ) :
    Function.Injective (closedPair A B k) ↔ closedConnecting A B hA hB k = 0 := by
  rw [← LinearMap.ker_eq_bot, ← closed_exact_union A B hA hB k, LinearMap.range_eq_bot]
  exact ModuleCat.hom_ext_iff.symm

/-- Vanishing one degree higher at the intersection suffices for unique gluing of compatible classes on closed sets. -/
theorem closed_compatible_glues_uniquely (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ)
    (hnext : IsZero (supportHomology (A ∩ B) (k+1)))
    (z : (supportHomology A k ⊞ supportHomology B k : ModuleCat ℚ))
    (hz : closedDifference A B k z = 0) : ∃! x, closedPair A B k x = z := by
  obtain ⟨x, hx⟩ := (closed_compatible_iff_glues A B hA hB k z).mp hz
  have hi := (closed_injective_iff_connecting_zero A B hA hB k).mpr (hnext.eq_of_src _ _)
  exact ⟨x, hx, fun y hy => hi (hy.trans hx.symm)⟩

/-- With both adjacent intersection groups zero, every pair of closed-support classes glues uniquely. -/
theorem closed_all_pairs_glue_uniquely (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ)
    (hnext : IsZero (supportHomology (A ∩ B) (k+1)))
    (hcurrent : IsZero (supportHomology (A ∩ B) k))
    (z : (supportHomology A k ⊞ supportHomology B k : ModuleCat ℚ)) :
    ∃! x, closedPair A B k x = z := by
  apply closed_compatible_glues_uniquely A B hA hB k hnext z
  have hzero : closedDifference A B k = 0 := hcurrent.eq_of_tgt _ _
  rw [hzero]
  rfl

/-- Two compact supports in a Hausdorff space admit unique gluing of compatible classes under the precise higher-degree vanishing hypothesis. -/
theorem compact_compatible_glues_uniquely [T2Space X] (A B : Set X) (hA : IsCompact A) (hB : IsCompact B)
    (k : ℕ) (hnext : IsZero (supportHomology (A ∩ B) (k+1)))
    (z : (supportHomology A k ⊞ supportHomology B k : ModuleCat ℚ))
    (hz : closedDifference A B k z = 0) : ∃! x, closedPair A B k x = z :=
  closed_compatible_glues_uniquely A B hA.isClosed hB.isClosed k hnext z hz

/-- Two compact supports admit unique gluing of every pair when both indicated intersection groups vanish. -/
theorem compact_all_pairs_glue_uniquely [T2Space X] (A B : Set X) (hA : IsCompact A) (hB : IsCompact B)
    (k : ℕ) (hnext : IsZero (supportHomology (A ∩ B) (k+1)))
    (hcurrent : IsZero (supportHomology (A ∩ B) k))
    (z : (supportHomology A k ⊞ supportHomology B k : ModuleCat ℚ)) :
    ∃! x, closedPair A B k x = z :=
  closed_all_pairs_glue_uniquely A B hA.isClosed hB.isClosed k hnext hcurrent z

end TernaryPoly.RationalRelativeSupport
