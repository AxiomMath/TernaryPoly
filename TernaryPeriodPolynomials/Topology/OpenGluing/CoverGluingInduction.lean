module

public import TernaryPeriodPolynomials.Topology.OpenGluing.BasisGluingInduction

@[expose] public section


namespace TernaryPoly.OpenBasisGluing
open TopologicalSpace Set

variable {X ι : Type} [TopologicalSpace X]

/-- Open subsets lying in one member of a fixed open cover. -/
def coverBasis (U : ι → Set X) : Set (Set X) := {s | IsOpen s ∧ ∃ i, s ⊆ U i}

theorem coverBasis_inter (U : ι → Set X) :
    ∀ b ∈ coverBasis U, ∀ c ∈ coverBasis U, b ∩ c ∈ coverBasis U := by
  rintro b ⟨hb,i,hi⟩ c ⟨hc,j,hj⟩
  exact ⟨hb.inter hc, i, inter_subset_left.trans hi⟩

/-- The open subsets of members of an open cover form an intersection-stable basis. -/
theorem coverBasis_isBasis (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = univ) : IsTopologicalBasis (coverBasis U) := by
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ hb => hb.1)
  intro x s hx hs
  have hxU : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxU
  exact ⟨s ∩ U i, ⟨hs.inter (hU i), i, inter_subset_right⟩, ⟨hx,hi⟩, inter_subset_left⟩

variable [SecondCountableTopology X]

/-- Local results on every open subset of each covering chart, binary gluing, and increasing
unions suffice for every open set of a second-countable space. -/
theorem open_induction_of_cover (P : Set X → Prop)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hLocal : ∀ i s, IsOpen s → s ⊆ U i → P s) (hEmpty : P ∅)
    (hGlue : ∀ b c, IsOpen b → IsOpen c → P b → P c → P (b ∩ c) → P (b ∪ c))
    (hIncreasing : ∀ s : ℕ → Set X, (∀ n, IsOpen (s n)) → Monotone s →
      (∀ n, P (s n)) → P (⋃ n, s n)) (s : Set X) (hs : IsOpen s) : P s := by
  apply open_induction_of_open (coverBasis_isBasis U hU hcover) ?_ hEmpty
    (coverBasis_inter U) hGlue ?_ s hs
  · rintro b ⟨hb,i,hi⟩
    exact hLocal i b hb hi
  · intro s ho hm hp
    exact hIncreasing s ho hm hp

end TernaryPoly.OpenBasisGluing
