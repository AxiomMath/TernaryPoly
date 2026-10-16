module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryPoint

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory HomologicalComplex RationalRelativeSingular RationalRelativeExcision
open RationalLocalOrientation RationalManifoldCompact BoundaryNeighborhood
variable {X H : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] [TopologicalSpace H]
  (A : Set X) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)
  {W : Set X}

/-- Push the genuine interior compact fundamental class through an ambient endpoint
collapse to obtain an actual boundary-relative homology class. -/
def relativeFundamentalClass (d : Deformation A W) (K : Set X)
    (hK : IsCompact K) (hKA : K ⊆ Aᶜ) (hcollapse : ∀ y ∈ Kᶜ, d.homotopy (1,y) ∈ A) :
    (relativeChains A).homology (n+2) :=
  homologyMap (fromNeighborhoodRelative d Kᶜ hcollapse) (n+2)
    (interiorFundamentalClass A hA n e o K hK hKA)

/-- Every interior point restriction of the actual boundary-relative class is its genuine
orientation generator. The larger compact support includes the complete homotopy trace of
the point, so no fixed-point hypothesis on the interior deformation is needed. -/
theorem relativeFundamentalClass_at_point (d : Deformation A W) (K : Set X)
    (hK : IsCompact K) (hKA : K ⊆ Aᶜ) (hcollapse : ∀ y ∈ Kᶜ, d.homotopy (1,y) ∈ A)
    (x : X) (hx : x ∉ A) :
    homologyMap (boundaryPointMap A x hx) (n+2)
      (relativeFundamentalClass A hA n e o d K hK hKA hcollapse) =
      homologyMap (pointExcisionMap x Aᶜ hx) (n+2) (o.generator ⟨x,hx⟩) := by
  let L := K ∪ d.trace {x}
  have hL : IsCompact L := hK.union (d.trace_isCompact {x} isClosed_singleton)
  have hLA : L ⊆ Aᶜ := Set.union_subset hKA
    (d.trace_subset_compl {x} (Set.singleton_subset_iff.mpr hx))
  have hKL : K ⊆ L := Set.subset_union_left
  have htrace : d.trace {x} ⊆ L := Set.subset_union_right
  have hc := interiorFundamentalClass_restriction A hA n e o L K hL hK hLA hKA hKL
  unfold relativeFundamentalClass
  rw [← hc]
  change (homologyMap (supportRestriction L K hKL) (n+2) ≫
    homologyMap (fromNeighborhoodRelative d Kᶜ hcollapse) (n+2) ≫
    homologyMap (boundaryPointMap A x hx) (n+2)) _ = _
  rw [← homologyMap_comp,← homologyMap_comp]
  rw [(collapsePointHomotopy d K L hcollapse hKL x hx htrace).homologyMap_eq]
  exact interiorFundamentalClass_at_point A hA n e o L hL hLA x
    (htrace (d.subset_trace {x} (Set.mem_singleton x)))

end TernaryPoly.RationalCompactBoundary
