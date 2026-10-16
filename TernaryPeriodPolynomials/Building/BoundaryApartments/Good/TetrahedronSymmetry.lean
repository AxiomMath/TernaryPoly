module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.VectorInitial

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

theorem goodTripleHeight_swap_last (a b c : NormalizedGoodVector) :
    goodTripleHeight (a, c, b) = goodTripleHeight (a, b, c) := by
  rw [goodTripleHeight_cyclic b a c, goodTripleHeight_swap a b c]

def SameGoodTetrahedronComplexity (first second : OrderedTetrahedron NormalizedGoodVector) : Prop :=
  ∀ bound, (TetrahedronBound goodTripleHeight bound first ↔ TetrahedronBound goodTripleHeight bound second) ∧
    tetrahedronTopCount goodTripleHeight bound first = tetrahedronTopCount goodTripleHeight bound second

theorem SameGoodTetrahedronComplexity.refl (tetrahedron : OrderedTetrahedron NormalizedGoodVector) :
    SameGoodTetrahedronComplexity tetrahedron tetrahedron := fun _ => ⟨Iff.rfl, rfl⟩

theorem SameGoodTetrahedronComplexity.symm {first second : OrderedTetrahedron NormalizedGoodVector}
    (same : SameGoodTetrahedronComplexity first second) : SameGoodTetrahedronComplexity second first :=
  fun bound => ⟨(same bound).1.symm, (same bound).2.symm⟩

theorem SameGoodTetrahedronComplexity.trans {first second third : OrderedTetrahedron NormalizedGoodVector}
    (first_same : SameGoodTetrahedronComplexity first second)
    (second_same : SameGoodTetrahedronComplexity second third) :
    SameGoodTetrahedronComplexity first third :=
  fun bound => ⟨(first_same bound).1.trans (second_same bound).1, (first_same bound).2.trans (second_same bound).2⟩

theorem goodTetrahedron_swap_first (a b c d : NormalizedGoodVector) :
    SameGoodTetrahedronComplexity (b, a, c, d) (a, b, c, d) := by
  classical
  intro bound
  constructor
  · simp only [TetrahedronBound, tetrahedronFace, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      goodTripleHeight_swap a b d, goodTripleHeight_swap a b c]
    tauto
  · unfold tetrahedronTopCount
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [tetrahedronFace]
    dsimp
    simp only [goodTripleHeight_swap a b d, goodTripleHeight_swap a b c]
    ac_rfl

theorem goodTetrahedron_swap_middle (a b c d : NormalizedGoodVector) :
    SameGoodTetrahedronComplexity (a, c, b, d) (a, b, c, d) := by
  classical
  intro bound
  constructor
  · simp only [TetrahedronBound, tetrahedronFace, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      goodTripleHeight_swap b c d, goodTripleHeight_swap_last a b c]
    tauto
  · unfold tetrahedronTopCount
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [tetrahedronFace]
    dsimp
    simp only [goodTripleHeight_swap b c d, goodTripleHeight_swap_last a b c]
    ac_rfl

theorem goodTetrahedron_swap_last (a b c d : NormalizedGoodVector) :
    SameGoodTetrahedronComplexity (a, b, d, c) (a, b, c, d) := by
  classical
  intro bound
  constructor
  · simp only [TetrahedronBound, tetrahedronFace, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      goodTripleHeight_swap_last b c d, goodTripleHeight_swap_last a c d]
    tauto
  · unfold tetrahedronTopCount
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [tetrahedronFace]
    dsimp
    simp only [goodTripleHeight_swap_last b c d, goodTripleHeight_swap_last a c d]
    ac_rfl

theorem goodTetrahedron_cycle_tail (a b c d : NormalizedGoodVector) :
    SameGoodTetrahedronComplexity (a, d, b, c) (a, b, c, d) :=
  (goodTetrahedron_swap_middle a b d c).trans (goodTetrahedron_swap_last a b c d)

theorem goodTetrahedron_cycle_head (a b c d : NormalizedGoodVector) :
    SameGoodTetrahedronComplexity (c, a, b, d) (a, b, c, d) :=
  (goodTetrahedron_swap_first a c b d).trans (goodTetrahedron_swap_middle a b c d)

theorem goodTetrahedron_cycle (a b c d : NormalizedGoodVector) :
    SameGoodTetrahedronComplexity (d, a, b, c) (a, b, c, d) :=
  (goodTetrahedron_swap_first a d b c).trans (goodTetrahedron_cycle_tail a b c d)

def tetrahedronVertex {α : Type*} (tetrahedron : OrderedTetrahedron α) : Fin 4 → α :=
  ![tetrahedron.1, tetrahedron.2.1, tetrahedron.2.2.1, tetrahedron.2.2.2]

def tetrahedronMoveFront {α : Type*} (tetrahedron : OrderedTetrahedron α) (index : Fin 4) :
    OrderedTetrahedron α := prependVertex (tetrahedronVertex tetrahedron index) (tetrahedronFace tetrahedron index)

theorem goodTetrahedron_move_front (tetrahedron : OrderedTetrahedron NormalizedGoodVector)
    (index : Fin 4) : SameGoodTetrahedronComplexity (tetrahedronMoveFront tetrahedron index) tetrahedron := by
  rcases tetrahedron with ⟨a, b, c, d⟩
  fin_cases index
  · exact SameGoodTetrahedronComplexity.refl _
  · exact goodTetrahedron_swap_first a b c d
  · exact goodTetrahedron_cycle_head a b c d
  · exact goodTetrahedron_cycle a b c d

theorem goodTetrahedron_cone_move_front (tetrahedron : OrderedTetrahedron NormalizedGoodVector)
    (vertex : NormalizedGoodVector) (pivot index : Fin 4) (different : index ≠ pivot) :
    ∃ next : Fin 4, next ≠ 0 ∧
      SameGoodTetrahedronComplexity (tetrahedronCone vertex tetrahedron index)
        (tetrahedronCone vertex (tetrahedronMoveFront tetrahedron pivot) next) := by
  rcases tetrahedron with ⟨a, b, c, d⟩
  fin_cases pivot <;> fin_cases index
  all_goals try exact (different rfl).elim
  · exact ⟨1, by decide, SameGoodTetrahedronComplexity.refl _⟩
  · exact ⟨2, by decide, SameGoodTetrahedronComplexity.refl _⟩
  · exact ⟨3, by decide, SameGoodTetrahedronComplexity.refl _⟩
  · exact ⟨1, by decide, SameGoodTetrahedronComplexity.refl _⟩
  · exact ⟨2, by decide, (goodTetrahedron_swap_middle vertex a b d).symm⟩
  · exact ⟨3, by decide, (goodTetrahedron_swap_middle vertex a b c).symm⟩
  · exact ⟨1, by decide, (goodTetrahedron_swap_middle vertex b c d).symm⟩
  · exact ⟨2, by decide, (goodTetrahedron_swap_middle vertex a c d).symm⟩
  · exact ⟨3, by decide, (goodTetrahedron_cycle_tail vertex a b c).symm⟩
  · exact ⟨1, by decide, (goodTetrahedron_cycle_tail vertex b c d).symm⟩
  · exact ⟨2, by decide, (goodTetrahedron_cycle_tail vertex a c d).symm⟩
  · exact ⟨3, by decide, (goodTetrahedron_cycle_tail vertex a b d).symm⟩

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
