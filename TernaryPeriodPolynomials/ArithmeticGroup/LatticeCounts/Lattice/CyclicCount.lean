module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Functional
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount

@[expose] public section


/-!
# Cyclic sublattices of index `p^r` counted as subgroups of `ℤ²`

Formalized by Claude Haiku 5.5.
Paper: Appendix C.

Transports `card_cyclicHNF` through the Hermite bijection `hnfEquiv`: the subgroups `L ≤ ℤ²` of index `p^r`
with cyclic quotient are counted by `p^r + p^(r-1)`.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

open Finset

/-- The Hermite bijection carries cyclic Hermite triples to cyclic subgroups of index `p^r`. -/
theorem card_cyclic_index_subgroups {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r) :
    Nat.card {L : AddSubgroup (ℤ × ℤ) // L.index = p ^ r ∧ IsAddCyclic ((ℤ × ℤ) ⧸ L)} =
      p ^ r + p ^ (r - 1) := by
  have hpos : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  have hiff : ∀ a : {t // t ∈ hnfData (p ^ r)}, a.1 ∈ cyclicHNF p r ↔
      IsAddCyclic ((ℤ × ℤ) ⧸ (hnfEquiv hpos a).1) := by
    intro a
    have hmem := a.2
    rw [mem_hnfData hpos] at hmem
    have hd : 0 < a.1.2.2 := by
      rcases Nat.eq_zero_or_pos a.1.2.2 with h | h
      · rw [h, mul_zero] at hmem
        exact absurd hmem.2.1.symm hpos.ne'
      · exact h
    have hlat : (hnfEquiv hpos a).1 = latOf a.1 := rfl
    rw [hlat]
    unfold cyclicHNF
    rw [mem_filter]
    constructor
    · rintro ⟨-, h2⟩
      exact (isAddCyclic_quot_latOf_iff hd).mpr h2
    · intro h
      exact ⟨a.2, (isAddCyclic_quot_latOf_iff hd).mp h⟩
  have e : {a : {t // t ∈ hnfData (p ^ r)} // a.1 ∈ cyclicHNF p r} ≃
      {L : {L : AddSubgroup (ℤ × ℤ) // L.index = p ^ r} // IsAddCyclic ((ℤ × ℤ) ⧸ L.1)} :=
    Equiv.subtypeEquiv (hnfEquiv hpos) hiff
  have e2 : {L : {L : AddSubgroup (ℤ × ℤ) // L.index = p ^ r} // IsAddCyclic ((ℤ × ℤ) ⧸ L.1)} ≃
      {L : AddSubgroup (ℤ × ℤ) // L.index = p ^ r ∧ IsAddCyclic ((ℤ × ℤ) ⧸ L)} :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun L : AddSubgroup (ℤ × ℤ) => L.index = p ^ r)
      (fun L => IsAddCyclic ((ℤ × ℤ) ⧸ L))
  have key : Nat.card {t // t ∈ cyclicHNF p r} =
      Nat.card {a : {t // t ∈ hnfData (p ^ r)} // a.1 ∈ cyclicHNF p r} := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨⟨x.1, by
        have hx := x.2
        unfold cyclicHNF at hx
        exact mem_of_mem_filter _ hx⟩, x.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [← Nat.card_congr (e.trans e2), ← key, Nat.card_eq_finsetCard, card_cyclicHNF hr]

end TernaryPeriodPolynomials.Argument.LatticeCounts
