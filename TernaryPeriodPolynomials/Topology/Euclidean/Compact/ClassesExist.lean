module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.ConvexNeighborhoods
public import TernaryPeriodPolynomials.Topology.Euclidean.Finite.ConvexClasses
public import TernaryPeriodPolynomials.Topology.Rational.Compact.Neighborhood

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanCompactClasses
open CategoryTheory Limits HomologicalComplex Set
open EuclideanCompactConvexNeighborhoods EuclideanFiniteConvex EuclideanConvexLocal EuclideanLocalHomology

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- Every compact subset of Euclidean space admits an actual top-degree relative class whose
point restrictions are all the fixed Euclidean generators. Uniqueness is proved separately. -/
theorem exists_compact_fundamental_class (K : Set E) (hK : IsCompact K) :
    ∃ c : (supportChains K).homology (n+2), ∀ (x : E) (hx : x ∈ K),
      homologyMap (pointMap K x hx) (n+2) c = localGenerator n x := by
  obtain ⟨s,A,hA,_,hKJ,_⟩ := exists_finite_convex_neighborhood (n+2) K Set.univ hK
    isOpen_univ (Set.subset_univ K)
  let J := ⋃ i ∈ s, A i
  have hKJ' : K ⊆ J := hKJ.trans interior_subset
  let cJ := finiteFamilyGenerator n s A (fun i _ => (hA i).1) (fun i _ => (hA i).2)
  refine ⟨homologyMap (supportRestriction J K hKJ') (n+2) cJ,?_⟩
  intro x hx
  rw [restriction_point_apply]
  exact finiteFamilyGenerator_at_point n s A (fun i _ => (hA i).1) (fun i _ => (hA i).2) x (hKJ' hx)

/-- Every actual relative homology class supported on a compact Euclidean set vanishes above
the ambient dimension, by finite-chain neighborhood lifting and finite-convex cofinality. -/
theorem compact_class_eq_zero_above (K : Set E) (hK : IsCompact K)
    (k : ℕ) (hk : n+2 < k) (c : (supportChains K).homology k) : c = 0 := by
  obtain ⟨L,_,hKL,cL,hc⟩ := RationalCompactNeighborhood.euclidean_compact_lift K hK k c
  obtain ⟨s,A,hA,_,hKJ,hJL⟩ := exists_finite_convex_neighborhood (n+2) K (interior L)
    hK isOpen_interior hKL
  let J := ⋃ i ∈ s, A i
  have hKJ' : K ⊆ J := hKJ.trans interior_subset
  have hJL' : J ⊆ L := hJL.trans interior_subset
  have hz := finite_family_above n s A (fun i _ => (hA i).1) (fun i _ => (hA i).2) k hk
  have hcJ : homologyMap (supportRestriction L J hJL') k cL = 0 :=
    (ModuleCat.subsingleton_of_isZero hz).elim _ _
  have hm : homologyMap (supportRestriction L J hJL') k ≫
      homologyMap (supportRestriction J K hKJ') k =
      homologyMap (supportRestriction L K (hKL.trans interior_subset)) k := by
    rw [← homologyMap_comp,supportRestriction_comp]
  have hh := congrArg (fun a => a cL) hm
  change homologyMap (supportRestriction J K hKJ') k
    (homologyMap (supportRestriction L J hJL') k cL) = _ at hh
  rw [hcJ,map_zero,hc] at hh
  exact hh.symm

/-- Actual compact-supported relative homology vanishes strictly above Euclidean dimension. -/
theorem compact_homology_isZero_above (K : Set E) (hK : IsCompact K) (k : ℕ) (hk : n+2 < k) :
    IsZero ((supportChains K).homology k) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun c e => (compact_class_eq_zero_above n K hK k hk c).trans
    (compact_class_eq_zero_above n K hK k hk e).symm⟩

end TernaryPoly.EuclideanCompactClasses
