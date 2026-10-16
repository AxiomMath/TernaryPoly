module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryDetection

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory HomologicalComplex RationalRelativeSingular RationalRelativeExcision
open RationalLocalOrientation RationalManifoldCompact BoundaryNeighborhood
variable {X H : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] [TopologicalSpace H]
  (A : Set X) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)
  {W : Set X}

/-- The endpoint collapse and actual interior point restrictions uniquely determine the
boundary-relative fundamental class. -/
theorem relativeFundamentalClass_unique (d : Deformation A W) (K : Set X)
    (hK : IsCompact K) (hKA : K ⊆ Aᶜ) (hcollapse : ∀ y ∈ Kᶜ, d.homotopy (1,y) ∈ A)
    (c : (relativeChains A).homology (n+2))
    (hc : ∀ x (hx : x ∉ A), homologyMap (boundaryPointMap A x hx) (n+2) c =
      homologyMap (pointExcisionMap x Aᶜ hx) (n+2) (o.generator ⟨x,hx⟩)) :
    c = relativeFundamentalClass A hA n e o d K hK hKA hcollapse := by
  have hAK : A ⊆ Kᶜ := fun x hx hk => hKA hk hx
  let q := toNeighborhoodRelative A Kᶜ hAK
  have hmono : Mono (homologyMap q (n+2)) :=
    toNeighborhoodRelative_homology_mono d Kᶜ hAK hcollapse (n+2)
  apply (ModuleCat.mono_iff_injective (homologyMap q (n+2))).mp hmono
  have image (z : (relativeChains A).homology (n+2))
      (hz : ∀ x (hx : x ∉ A), homologyMap (boundaryPointMap A x hx) (n+2) z =
        homologyMap (pointExcisionMap x Aᶜ hx) (n+2) (o.generator ⟨x,hx⟩)) :
      homologyMap q (n+2) z = interiorFundamentalClass A hA n e o K hK hKA := by
    apply interiorFundamentalClass_unique A hA n e o K hK hKA
    intro x hx
    have hq : q ≫ supportPointMap K x hx = boundaryPointMap A x (hKA hx) := by
      dsimp [q,toNeighborhoodRelative,supportPointMap,boundaryPointMap]
      erw [RationalRelativeSingular.relativeMap_comp]
      rfl
    change (homologyMap q (n+2) ≫ homologyMap (supportPointMap K x hx) (n+2)) z = _
    rw [← homologyMap_comp,hq]
    exact hz x (hKA hx)
  exact (image c hc).trans (image _
    (relativeFundamentalClass_at_point A hA n e o d K hK hKA hcollapse)).symm

include hA e in
/-- A compact pair with oriented Euclidean-manifold interior and a genuine ambient
boundary-neighborhood collapse has a unique actual relative fundamental class. -/
theorem existsUnique_relativeFundamentalClass (d : Deformation A W) (N : Set X)
    (hN : IsOpen N) (hAN : A ⊆ N) (hcollapse : ∀ y ∈ N, d.homotopy (1,y) ∈ A) :
    ∃! c : (relativeChains A).homology (n+2), ∀ x (hx : x ∉ A),
      homologyMap (boundaryPointMap A x hx) (n+2) c =
        homologyMap (pointExcisionMap x Aᶜ hx) (n+2) (o.generator ⟨x,hx⟩) := by
  have hK : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hKA : Nᶜ ⊆ Aᶜ := Set.compl_subset_compl.mpr hAN
  have hc : ∀ y ∈ (Nᶜ)ᶜ, d.homotopy (1,y) ∈ A := by simpa only [compl_compl] using hcollapse
  refine ⟨relativeFundamentalClass A hA n e o d Nᶜ hK hKA hc,
    relativeFundamentalClass_at_point A hA n e o d Nᶜ hK hKA hc,?_⟩
  intro c h
  exact relativeFundamentalClass_unique A hA n e o d Nᶜ hK hKA hc c h

end TernaryPoly.RationalCompactBoundary
