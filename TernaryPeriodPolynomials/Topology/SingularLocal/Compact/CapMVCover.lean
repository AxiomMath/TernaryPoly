module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVScalarExcision

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open TopologicalSpace SphereOddDegree

/-- The common refinement by intersections of members of two actual open covers. -/
def intersectCover {X : TopCat.{0}} (𝒰 𝒱 : OpenCoverData X) : OpenCoverData X where
  sets := {S | ∃ U ∈ 𝒰.sets, ∃ V ∈ 𝒱.sets, S = U ∩ V}
  isOpen_mem := by
    rintro _ ⟨U,hU,V,hV,rfl⟩
    exact (𝒰.isOpen_mem U hU).inter (𝒱.isOpen_mem V hV)
  covers x := by
    obtain ⟨U,hU,hxU⟩ := 𝒰.covers x
    obtain ⟨V,hV,hxV⟩ := 𝒱.covers x
    exact ⟨U ∩ V,⟨U,hU,V,hV,rfl⟩,hxU,hxV⟩

/-- A simplex small for the common refinement is small for the first actual cover. -/
theorem intersectCover_left {X : TopCat.{0}} (𝒰 𝒱 : OpenCoverData X) (n : ℕ)
    (σ : singularSimplices X n) (hσ : IsSmallSimplex (intersectCover 𝒰 𝒱) σ) : IsSmallSimplex 𝒰 σ := by
  obtain ⟨_,⟨U,hU,V,_,rfl⟩,hσ⟩ := hσ
  exact ⟨U,hU,hσ.trans Set.inter_subset_left⟩

/-- A simplex small for the common refinement is small for the second actual cover. -/
theorem intersectCover_right {X : TopCat.{0}} (𝒰 𝒱 : OpenCoverData X) (n : ℕ)
    (σ : singularSimplices X n) (hσ : IsSmallSimplex (intersectCover 𝒰 𝒱) σ) : IsSmallSimplex 𝒱 σ := by
  obtain ⟨_,⟨U,_,V,hV,rfl⟩,hσ⟩ := hσ
  exact ⟨V,hV,hσ.trans Set.inter_subset_right⟩

/-- The common support/open refinement also localizes the intersected support into the
actual intersection of the two opens. -/
theorem intersectSupportCover_intersection {X : TopCat.{0}} (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (U D : Opens X) (hKU : K ⊆ U) (hLD : L ⊆ D)
    (n : ℕ) (σ : singularSimplices X n)
    (hσ : IsSmallSimplex (intersectCover (supportOpenCover K hK U hKU)
      (supportOpenCover L hL D hLD)) σ) :
    IsSmallSimplex (supportOpenCover (K ∩ L) (hK.inter hL) (U ⊓ D)
      (Set.inter_subset_inter hKU hLD)) σ := by
  obtain ⟨_,⟨A,hA,B,hB,rfl⟩,hσ⟩ := hσ
  change A = Kᶜ ∨ A = (U : Set X) at hA
  change B = Lᶜ ∨ B = (D : Set X) at hB
  rcases hA with rfl | rfl
  · refine ⟨(K ∩ L)ᶜ,Or.inl rfl,?_⟩
    exact fun x hx h => (hσ hx).1 h.1
  · rcases hB with rfl | rfl
    · refine ⟨(K ∩ L)ᶜ,Or.inl rfl,?_⟩
      exact fun x hx h => (hσ hx).2 h.2
    · exact ⟨(U ⊓ D : Opens X),Or.inr rfl,hσ⟩

end TernaryPoly.SingularLocalCompactCapMV
