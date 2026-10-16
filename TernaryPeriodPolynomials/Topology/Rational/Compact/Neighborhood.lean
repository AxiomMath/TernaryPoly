module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.NeighborhoodContinuity
public import TernaryPeriodPolynomials.Topology.Euclidean.Convex.LocalNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactNeighborhood
open CategoryTheory Limits HomologicalComplex

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The generic continuity restriction is literally the existing Euclidean support map. -/
theorem restriction_eq_euclidean (K L : Set E) (h : L ⊆ K) :
    restriction K L h = EuclideanConvexLocal.supportRestriction K L h := rfl

/-- Restriction to singleton support is literally the existing local homology point map. -/
theorem restriction_singleton_eq_pointMap (K : Set E) (x : E) (hx : x ∈ K) :
    restriction K {x} (Set.singleton_subset_iff.mpr hx) =
      EuclideanConvexLocal.pointMap K x hx := rfl

/-- Genuine Euclidean compact-neighborhood lifting uses the existing support restriction. -/
theorem euclidean_compact_lift (K : Set E) (hK : IsCompact K)
    (n : ℕ) (c : (EuclideanConvexLocal.supportChains K).homology n) :
    ∃ (L : Set E) (_ : IsCompact L) (hKL : K ⊆ interior L)
      (cL : (EuclideanConvexLocal.supportChains L).homology n),
      homologyMap (EuclideanConvexLocal.supportRestriction L K
        (hKL.trans interior_subset)) n cL = c :=
  exists_compact_lift K hK n c

/-- Vanishing of the actual Euclidean local image gives vanishing on a compact
neighborhood through the existing support map, in every homological degree. -/
theorem euclidean_local_zero_witness (L : Set E) (x : E) (hx : x ∈ interior L)
    (n : ℕ) (c : (EuclideanConvexLocal.supportChains L).homology n)
    (hc : homologyMap (EuclideanConvexLocal.pointMap L x (interior_subset hx)) n c = 0) :
    ∃ (K' : Set E) (_ : IsCompact K') (_ : x ∈ interior K') (hK'L : K' ⊆ L),
      homologyMap (EuclideanConvexLocal.supportRestriction L K' hK'L) n c = 0 :=
  exists_local_zero_witness L x hx n c hc

/-- Equality on a Euclidean compact support has a compact-neighborhood witness using
the existing support restrictions, with no dimension or rank hypothesis. -/
theorem euclidean_compact_equality_witness (K L : Set E) (hK : IsCompact K)
    (hKL : K ⊆ interior L) (n : ℕ) (c e : (EuclideanConvexLocal.supportChains L).homology n)
    (hce : homologyMap (EuclideanConvexLocal.supportRestriction L K
      (hKL.trans interior_subset)) n c =
      homologyMap (EuclideanConvexLocal.supportRestriction L K
        (hKL.trans interior_subset)) n e) :
    ∃ (K' : Set E) (_ : IsCompact K') (_ : K ⊆ interior K') (hK'L : K' ⊆ L),
      homologyMap (EuclideanConvexLocal.supportRestriction L K' hK'L) n c =
        homologyMap (EuclideanConvexLocal.supportRestriction L K' hK'L) n e :=
  exists_compact_equality_witness K L hK hKL n c e hce

end TernaryPoly.RationalCompactNeighborhood
