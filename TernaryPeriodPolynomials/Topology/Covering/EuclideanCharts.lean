module

public import TernaryPeriodPolynomials.Topology.Covering.EuclideanChartsNeighborhoods
public import TernaryPeriodPolynomials.Topology.OpenGluing.CoverGluingInduction

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringEuclideanCharts
open CategoryTheory TopologicalSpace
open EquivariantSingularSmall
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]
  {H : Type} [TopologicalSpace H] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- A point-indexed family of actual Euclidean covering neighborhoods. -/
def coverOpen (x : B) : Opens B := (neighborhood (G := G) p n e x ⊤ (by trivial)).openSet

/-- Each indexed point belongs to its own covering neighborhood. -/
theorem mem_coverOpen (x : B) : x ∈ coverOpen (G := G) p n e x :=
  (neighborhood (G := G) p n e x ⊤ (by trivial)).mem_openSet

/-- Every member of the actual point-indexed cover is genuinely homeomorphic to Euclidean space. -/
def coverHomeomorph (x : B) : coverOpen (G := G) p n e x ≃ₜ EuclideanSpace ℝ (Fin (n+2)) :=
  (neighborhood (G := G) p n e x ⊤ (by trivial)).homeomorph

/-- Every member has a continuous section of its actual restricted covering projection. -/
def coverSection (x : B) : Section p (coverOpen (G := G) p n e x) :=
  (neighborhood (G := G) p n e x ⊤ (by trivial)).lift

/-- The selected section has the literal right-inverse identity in TopCat. -/
theorem coverSection_rightInverse (x : B) :
    (coverSection (G := G) p n e x).map ≫ restrictedProjection p (coverOpen (G := G) p n e x : Set B) = 𝟙 _ :=
  (coverSection (G := G) p n e x).right_inv

/-- The actual Euclidean covering neighborhoods cover the entire base. -/
theorem cover_iUnion : (⋃ x : B, (coverOpen (G := G) p n e x : Set B)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨x,mem_coverOpen (G := G) p n e x⟩

/-- Every smaller open subset of a covering neighborhood retains its genuine continuous section. -/
def coverSectionRestrict (x : B) (D : Opens B) (hD : D ≤ coverOpen (G := G) p n e x) : Section p D :=
  Section.restrict p (coverSection (G := G) p n e x) D hD

/-- The further restricted section is still a literal right inverse of the actual restricted projection. -/
theorem coverSectionRestrict_rightInverse (x : B) (D : Opens B) (hD : D ≤ coverOpen (G := G) p n e x) :
    (coverSectionRestrict (G := G) p n e x D hD).map ≫ restrictedProjection p (D : Set B) = 𝟙 _ :=
  (coverSectionRestrict (G := G) p n e x D hD).right_inv

/-- This actual point-indexed cover supplies the intersection-stable basis used by open-cover gluing. -/
theorem coverBasis_isBasis : IsTopologicalBasis
    (OpenBasisGluing.coverBasis (fun x : B => (coverOpen (G := G) p n e x : Set B))) :=
  OpenBasisGluing.coverBasis_isBasis (fun x : B => (coverOpen (G := G) p n e x : Set B))
    (fun x => (coverOpen (G := G) p n e x).isOpen) (cover_iUnion (G := G) p n e)

/-- Every member of that genuine gluing basis has an actual continuous covering section. -/
theorem coverBasis_section (D : Opens B)
    (hD : (D : Set B) ∈ OpenBasisGluing.coverBasis (fun x : B => (coverOpen (G := G) p n e x : Set B))) :
    Nonempty (Section p D) := by
  obtain ⟨_,x,hDx⟩ := hD
  exact ⟨coverSectionRestrict (G := G) p n e x D hDx⟩

/-- Consumer: every point has an arbitrarily small actual Euclidean chart with an actual
continuous section, and the chosen global family covers the base. -/
theorem covering_euclidean_consumer (x : B) (W : Opens B) (hxW : x ∈ W) :
    (∃ D : Opens B, x ∈ D ∧ D ≤ W ∧ Nonempty (D ≃ₜ EuclideanSpace ℝ (Fin (n+2))) ∧
      ∃ s : TopCat.of D ⟶ TopCat.of (p ⁻¹' (D : Set B)), s ≫ restrictedProjection p (D : Set B) = 𝟙 _) ∧
    (⋃ y : B, (coverOpen (G := G) p n e y : Set B)) = Set.univ := by
  let d := neighborhood (G := G) p n e x W hxW
  exact ⟨⟨d.openSet,d.mem_openSet,d.subset,⟨d.homeomorph⟩,d.lift.map,d.lift.right_inv⟩,
    cover_iUnion (G := G) p n e⟩

end TernaryPoly.CoveringEuclideanCharts
