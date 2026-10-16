module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.Reduction
public import TernaryPeriodPolynomials.Analysis.Compact.DenseImage
public import Mathlib.GroupTheory.Index

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCompactQuotient
open SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceFlagCoordinates
  SymmetricSpaceSiegelReduction

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- The explicit Siegel box proves compactness of any Hausdorff integral quotient extension
whose corner map and dense interior quotient have the stated literal compatibility. -/
theorem compact_of_integral_invariant (q : Space → Y) (hq : DenseRange q)
    (j : Corner → Y) (hj : Continuous j)
    (hcompat : ∀ S, j (cornerEmbedding S) = q S)
    (hinv : ∀ (g : IntegralGL) S, q (act (realIntegral g) S) = q S) : CompactSpace Y := by
  apply CompactDenseImage.compactSpace (isCompact_cornerBox (1/2) 2) hj hq
  rintro _ ⟨S,rfl⟩
  obtain ⟨g,hg,-⟩ := exists_orbit_representative_in_compact_box S
  exact ⟨cornerEmbedding (act (realIntegral g) S),hg,(hcompat _).trans (hinv g S)⟩

/-- A finite-index subgroup needs finitely many translated corner boxes, not a new
reduction theorem. All topology and actual chart compatibility hypotheses remain explicit. -/
theorem compact_of_finite_index_invariant (H : Subgroup IntegralGL) [H.FiniteIndex]
    (q : Space → Y) (hq : DenseRange q)
    (j : IntegralGL → Corner → Y) (hj : ∀ g, Continuous (j g))
    (hcompat : ∀ g S, j g (cornerEmbedding S) = q (act (realIntegral g) S))
    (hinv : ∀ (h : H) S, q (act (realIntegral h.val) S) = q S) : CompactSpace Y := by
  let K : Set Y := ⋃ c : IntegralGL ⧸ H, j (c.out⁻¹) '' cornerBox (1/2) 2
  have hK : IsCompact K := isCompact_iUnion fun c =>
    (isCompact_cornerBox (1/2) 2).image (hj c.out⁻¹)
  have hcover : Set.range q ⊆ K := by
    rintro _ ⟨S,rfl⟩
    obtain ⟨g,hg,-⟩ := exists_orbit_representative_in_compact_box S
    obtain ⟨h,hh⟩ := QuotientGroup.mk_out_eq_mul (s := H) g
    apply Set.mem_iUnion.mpr
    refine ⟨(QuotientGroup.mk g : IntegralGL ⧸ H),
      cornerEmbedding (act (realIntegral g) S),hg,?_⟩
    rw [hcompat,hh]
    simp only [mul_inv_rev, map_mul, map_inv, act_mul]
    have hi : act ((realIntegral g)⁻¹) (act (realIntegral g) S) = S := by
      rw [← act_mul,inv_mul_cancel,act_one]
    rw [hi]
    exact hinv h⁻¹ S
  have he : K = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hq.closure_range]
    exact closure_minimal hcover hK.isClosed
  exact ⟨he ▸ hK⟩

end TernaryPoly.SymmetricSpaceCompactQuotient
