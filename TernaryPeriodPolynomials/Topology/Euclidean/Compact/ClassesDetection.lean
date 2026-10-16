module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.ClassesExist

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanCompactClasses
open CategoryTheory Limits HomologicalComplex Set
open EuclideanCompactConvexNeighborhoods EuclideanFiniteConvex EuclideanConvexLocal EuclideanLocalHomology

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- Actual top-degree classes on arbitrary compact Euclidean sets are detected by all point
restrictions. Finite bounding-chain witnesses turn zero local values into neighborhood zeroes. -/
theorem compact_class_eq_zero_of_points (K : Set E) (hK : IsCompact K)
    (c : (supportChains K).homology (n+2))
    (hc : ∀ (x : E) (hx : x ∈ K), homologyMap (pointMap K x hx) (n+2) c = 0) : c = 0 := by
  classical
  obtain ⟨L,_,hKL,cL,hcL⟩ := RationalCompactNeighborhood.euclidean_compact_lift K hK (n+2) c
  have hzero : ∀ x : K, homologyMap (pointMap L x.val (interior_subset (hKL x.property))) (n+2) cL = 0 := by
    intro x
    rw [← restriction_point_apply L K (hKL.trans interior_subset) x.val x.property (n+2) cL,hcL]
    exact hc x.val x.property
  have hex := fun x : K => RationalCompactNeighborhood.euclidean_local_zero_witness L x.val
    (hKL x.property) (n+2) cL (hzero x)
  choose N hN hxN hNL hzeroN using hex
  obtain ⟨s,A,j,hA,_,hKJ⟩ := exists_finite_convex_refinement (n+2) K hK
    (fun x : K => interior (N x)) (fun _ => isOpen_interior) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxN ⟨x,hx⟩⟩)
  let J := ⋃ i ∈ s, A i
  have hAJ : ∀ i, A i ⊆ N (j i) := fun i => (hA i).2.2.trans interior_subset
  have hJL : J ⊆ L := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_iUnion₂.mp hx
    exact hNL (j i) (hAJ i hi)
  have hKJ' : K ⊆ J := hKJ.trans interior_subset
  let cJ := homologyMap (supportRestriction L J hJL) (n+2) cL
  have hcJ : cJ = 0 := by
    apply (finite_family_eq_zero_iff n s A (fun i _ => (hA i).1)
      (fun i _ => (hA i).2.1) cJ).mpr
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_iUnion₂.mp hx
    change homologyMap (pointMap J x hx) (n+2)
      (homologyMap (supportRestriction L J hJL) (n+2) cL) = 0
    rw [restriction_point_apply]
    rw [← restriction_point_apply L (N (j i)) (hNL (j i)) x (hAJ i hi) (n+2) cL,
      hzeroN (j i),map_zero]
  have hm : homologyMap (supportRestriction L J hJL) (n+2) ≫
      homologyMap (supportRestriction J K hKJ') (n+2) =
      homologyMap (supportRestriction L K (hKL.trans interior_subset)) (n+2) := by
    rw [← homologyMap_comp,supportRestriction_comp]
  have hh := congrArg (fun a => a cL) hm
  change homologyMap (supportRestriction J K hKJ') (n+2) cJ = _ at hh
  rw [hcJ,map_zero,hcL] at hh
  exact hh.symm

/-- Point restrictions jointly detect actual top-degree homology of any compact Euclidean support. -/
theorem compact_class_detect (K : Set E) (hK : IsCompact K)
    (c e : (supportChains K).homology (n+2))
    (hce : ∀ (x : E) (hx : x ∈ K), homologyMap (pointMap K x hx) (n+2) c =
      homologyMap (pointMap K x hx) (n+2) e) : c = e := by
  apply sub_eq_zero.mp
  apply compact_class_eq_zero_of_points n K hK (c-e)
  intro x hx
  rw [map_sub,hce x hx,sub_self]

end TernaryPoly.EuclideanCompactClasses
