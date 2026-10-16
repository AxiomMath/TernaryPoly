module

public import TernaryPeriodPolynomials.Topology.Euclidean.BoxBasis

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanBoxBasis
open TopologicalSpace Set

variable {ι X : Type} [TopologicalSpace X]

/-- Pull the coordinate-box basis back along a genuine homeomorphism. -/
def transportedBoxes (e : X ≃ₜ (ι → ℝ)) : Set (Set X) := Set.preimage e '' boxes

theorem transportedBoxes_basis [Fintype ι] (e : X ≃ₜ (ι → ℝ)) :
    IsTopologicalBasis (transportedBoxes e) :=
  Topology.IsInducing.isTopologicalBasis e.isInducing boxes_basis

theorem transportedBoxes_inter (e : X ≃ₜ (ι → ℝ)) :
    ∀ b ∈ transportedBoxes e, ∀ c ∈ transportedBoxes e, b ∩ c ∈ transportedBoxes e := by
  rintro b ⟨b',hb,rfl⟩ c ⟨c',hc,rfl⟩
  exact ⟨b' ∩ c', boxes_inter b' hb c' hc, rfl⟩

/-- Every nonempty transported box is homeomorphic to the entire ambient model. -/
theorem transportedBox_nonempty_homeomorph (e : X ≃ₜ (ι → ℝ)) (s : Set X)
    (hs : s ∈ transportedBoxes e) (hne : s.Nonempty) : Nonempty (s ≃ₜ X) := by
  obtain ⟨b,⟨l,u,rfl⟩,rfl⟩ := hs
  obtain ⟨x,hx⟩ := hne
  exact ⟨(e.sets rfl).trans ((boxHomeomorph l u (fun i => lt_trans (hx i).1 (hx i).2)).trans e.symm)⟩

/-- An intersection-stable Euclidean basis whose nonempty elements are Euclidean. -/
theorem euclidean_basis (m : ℕ) :
    ∃ B : Set (Set (EuclideanSpace ℝ (Fin m))), IsTopologicalBasis B ∧
      (∀ b ∈ B, ∀ c ∈ B, b ∩ c ∈ B) ∧
      (∀ b ∈ B, b.Nonempty → Nonempty (b ≃ₜ EuclideanSpace ℝ (Fin m))) := by
  let e := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  exact ⟨transportedBoxes e, transportedBoxes_basis e, transportedBoxes_inter e,
    transportedBox_nonempty_homeomorph e⟩

end TernaryPoly.EuclideanBoxBasis
