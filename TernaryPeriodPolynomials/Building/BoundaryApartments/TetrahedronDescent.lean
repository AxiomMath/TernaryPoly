module

public import Mathlib

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

abbrev OrderedTriple (α : Type*) := α × α × α
abbrev OrderedTetrahedron (α : Type*) := α × α × α × α

def tripleConeFaces {α : Type*} (vertex : α) (triple : OrderedTriple α) : Fin 3 → OrderedTriple α :=
  ![(vertex, triple.2.1, triple.2.2), (vertex, triple.1, triple.2.2), (vertex, triple.1, triple.2.1)]

def tetrahedronFace {α : Type*} (tetrahedron : OrderedTetrahedron α) : Fin 4 → OrderedTriple α :=
  ![(tetrahedron.2.1, tetrahedron.2.2.1, tetrahedron.2.2.2),
    (tetrahedron.1, tetrahedron.2.2.1, tetrahedron.2.2.2),
    (tetrahedron.1, tetrahedron.2.1, tetrahedron.2.2.2),
    (tetrahedron.1, tetrahedron.2.1, tetrahedron.2.2.1)]

def prependVertex {α : Type*} (vertex : α) (triple : OrderedTriple α) : OrderedTetrahedron α :=
  (vertex, triple.1, triple.2.1, triple.2.2)

def tetrahedronCone {α : Type*} (vertex : α) (tetrahedron : OrderedTetrahedron α)
    (index : Fin 4) : OrderedTetrahedron α := prependVertex vertex (tetrahedronFace tetrahedron index)

def tetrahedronValue {α V : Type*} [AddCommGroup V] (value : OrderedTriple α → V)
    (tetrahedron : OrderedTetrahedron α) : V :=
  value (tetrahedronFace tetrahedron 0) - value (tetrahedronFace tetrahedron 1) +
    value (tetrahedronFace tetrahedron 2) - value (tetrahedronFace tetrahedron 3)

def TetrahedronBound {α : Type*} (height : OrderedTriple α → ℕ) (bound : ℕ)
    (tetrahedron : OrderedTetrahedron α) : Prop :=
  ∀ index, height (tetrahedronFace tetrahedron index) ≤ bound

def tetrahedronTopCount {α : Type*} (height : OrderedTriple α → ℕ) (bound : ℕ)
    (tetrahedron : OrderedTetrahedron α) : ℕ :=
  (Finset.univ.filter (fun index => height (tetrahedronFace tetrahedron index) = bound)).card

theorem tetrahedronValue_cone {α V : Type*} [AddCommGroup V]
    (value : OrderedTriple α → V) (tetrahedron : OrderedTetrahedron α) (vertex : α) :
    tetrahedronValue value tetrahedron =
      tetrahedronValue value (tetrahedronCone vertex tetrahedron 0) -
      tetrahedronValue value (tetrahedronCone vertex tetrahedron 1) +
      tetrahedronValue value (tetrahedronCone vertex tetrahedron 2) -
      tetrahedronValue value (tetrahedronCone vertex tetrahedron 3) := by
  rcases tetrahedron with ⟨first, second, third, fourth⟩
  change value (second, third, fourth) - value (first, third, fourth) +
      value (first, second, fourth) - value (first, second, third) =
    (value (second, third, fourth) - value (vertex, third, fourth) +
      value (vertex, second, fourth) - value (vertex, second, third)) -
    (value (first, third, fourth) - value (vertex, third, fourth) +
      value (vertex, first, fourth) - value (vertex, first, third)) +
    (value (first, second, fourth) - value (vertex, second, fourth) +
      value (vertex, first, fourth) - value (vertex, first, second)) -
    (value (first, second, third) - value (vertex, second, third) +
      value (vertex, first, third) - value (vertex, first, second))
  abel

/-- Data for determinant descent. The refinement clause permits one child
to be the defining cone of a maximal face; every other child has fewer
faces attaining the same bound. -/
structure TetrahedronDescentData (α V : Type*) [AddCommGroup V] where
  height : OrderedTriple α → ℕ
  initial : OrderedTriple α → V
  reduce : OrderedTriple α → α
  decrease : ∀ triple, 1 < height triple → ∀ index,
    height (tripleConeFaces (reduce triple) triple index) < height triple
  initial_relation : ∀ tetrahedron, TetrahedronBound height 1 tetrahedron →
    tetrahedronValue initial tetrahedron = 0
  refine_relation : ∀ bound tetrahedron, 1 < bound → TetrahedronBound height bound tetrahedron →
    (∃ index, height (tetrahedronFace tetrahedron index) = bound) →
    ∃ pivot : Fin 4, ∃ vertex : α,
      height (tetrahedronFace tetrahedron pivot) = bound ∧
      vertex = reduce (tetrahedronFace tetrahedron pivot) ∧
      ∀ index, index ≠ pivot →
        TetrahedronBound height bound (tetrahedronCone vertex tetrahedron index) ∧
        tetrahedronTopCount height bound (tetrahedronCone vertex tetrahedron index) <
          tetrahedronTopCount height bound tetrahedron

def descendedTripleValue {α V : Type*} [AddCommGroup V] (data : TetrahedronDescentData α V)
    (triple : OrderedTriple α) : V :=
  if _small : data.height triple ≤ 1 then data.initial triple else
    descendedTripleValue data (tripleConeFaces (data.reduce triple) triple 0) -
    descendedTripleValue data (tripleConeFaces (data.reduce triple) triple 1) +
    descendedTripleValue data (tripleConeFaces (data.reduce triple) triple 2)
termination_by data.height triple
decreasing_by all_goals exact data.decrease triple (by omega) _

theorem descendedTripleValue_small {α V : Type*} [AddCommGroup V] (data : TetrahedronDescentData α V)
    (triple : OrderedTriple α) (small : data.height triple ≤ 1) :
    descendedTripleValue data triple = data.initial triple := by
  rw [descendedTripleValue, dite_eq_left small]

theorem descendedTripleValue_defining_cone {α V : Type*} [AddCommGroup V]
    (data : TetrahedronDescentData α V) (triple : OrderedTriple α) (large : 1 < data.height triple) :
    tetrahedronValue (descendedTripleValue data) (prependVertex (data.reduce triple) triple) = 0 := by
  have definition := descendedTripleValue.eq_def data triple
  rw [dite_eq_right (by omega : ¬data.height triple ≤ 1)] at definition
  change descendedTripleValue data triple -
    descendedTripleValue data (tripleConeFaces (data.reduce triple) triple 0) +
    descendedTripleValue data (tripleConeFaces (data.reduce triple) triple 1) -
    descendedTripleValue data (tripleConeFaces (data.reduce triple) triple 2) = 0
  rw [definition]
  abel

theorem descendedTripleValue_bounded_relation {α V : Type*} [AddCommGroup V]
    (data : TetrahedronDescentData α V) (bound : ℕ) (tetrahedron : OrderedTetrahedron α)
    (bounded : TetrahedronBound data.height bound tetrahedron) :
    tetrahedronValue (descendedTripleValue data) tetrahedron = 0 := by
  have induction : ∀ bound, ∀ tetrahedron : OrderedTetrahedron α,
      TetrahedronBound data.height bound tetrahedron →
        tetrahedronValue (descendedTripleValue data) tetrahedron = 0 := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound previous =>
      by_cases small : bound ≤ 1
      · intro tetrahedron bounded
        have face_small (index : Fin 4) : data.height (tetrahedronFace tetrahedron index) ≤ 1 :=
          (bounded index).trans small
        simp only [tetrahedronValue, descendedTripleValue_small data _ (face_small _)]
        exact data.initial_relation tetrahedron face_small
      · have by_count : ∀ count, ∀ tetrahedron : OrderedTetrahedron α,
            tetrahedronTopCount data.height bound tetrahedron = count →
            TetrahedronBound data.height bound tetrahedron →
              tetrahedronValue (descendedTripleValue data) tetrahedron = 0 := by
          intro count
          induction count using Nat.strong_induction_on with
          | h count smaller_count =>
            intro tetrahedron count_eq bounded
            by_cases attained : ∃ index, data.height (tetrahedronFace tetrahedron index) = bound
            · obtain ⟨pivot, vertex, pivot_height, vertex_eq, children⟩ :=
                data.refine_relation bound tetrahedron (by omega) bounded attained
              have children_zero (index : Fin 4) :
                  tetrahedronValue (descendedTripleValue data) (tetrahedronCone vertex tetrahedron index) = 0 := by
                by_cases same : index = pivot
                · subst index
                  rw [tetrahedronCone, vertex_eq]
                  apply descendedTripleValue_defining_cone
                  omega
                · exact smaller_count _ (count_eq ▸ (children index same).2) _ rfl (children index same).1
              rw [tetrahedronValue_cone _ tetrahedron vertex]
              simp only [children_zero, sub_self, add_zero]
            · apply previous (bound - 1) (by omega) tetrahedron
              intro index
              have upper := bounded index
              have strict : data.height (tetrahedronFace tetrahedron index) ≠ bound :=
                fun equality => attained ⟨index, equality⟩
              omega
        intro tetrahedron bounded
        exact by_count _ tetrahedron rfl bounded
  exact induction bound tetrahedron bounded

theorem descendedTripleValue_relation {α V : Type*} [AddCommGroup V]
    (data : TetrahedronDescentData α V) (tetrahedron : OrderedTetrahedron α) :
    tetrahedronValue (descendedTripleValue data) tetrahedron = 0 := by
  apply descendedTripleValue_bounded_relation data
    (Finset.univ.sup (fun index => data.height (tetrahedronFace tetrahedron index))) tetrahedron
  intro index
  exact Finset.le_sup (f := fun index : Fin 4 => data.height (tetrahedronFace tetrahedron index))
    (Finset.mem_univ index)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
