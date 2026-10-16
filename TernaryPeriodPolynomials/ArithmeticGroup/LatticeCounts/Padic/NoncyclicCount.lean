module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Surjective

@[expose] public section


/-!
# Count of noncyclic `ℤ_p`-lattices of index `p^r`: obligation (a), count level

Formalized by Claude Haiku 5.5.

Proved here, for `r ≥ 2` and every prime `p`: the number of `ℤ_p`-lattices `Λ ⊆ ℤ_p²` of index `p^r`
with `ℤ_p²/Λ` not cyclic is `∑_{i < r-1} p^i`. This is the total count `∑_{i ≤ r} p^i`
(`card_lattices`) minus the cyclic count `p^r + p^{r-1}` (`card_cyclic_lattices`). It equals the
number of index-`p^{r-2}` lattices, as the scaling bijection `Λ' ↦ pΛ'` would give.

NOT proved here: the scaling bijection `Λ' ↦ pΛ'` itself.
With that lemma, `Submodule.index_map_of_injective` and `index_prod` give
`[ℤ_p² : pΛ'] = p² · [ℤ_p² : Λ']`.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

open PadicInt

/-- The noncyclic `ℤ_p`-lattices of index `p^r`, `r ≥ 2`, number `∑_{i < r-1} p^i`. -/
theorem card_noncyclic_lattices (p r : ℕ) [hp : Fact p.Prime] (hr : 2 ≤ r) :
    Nat.card {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ r ∧
        ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} =
      ∑ i ∈ Finset.range (r - 1), p ^ i := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have hpos : 0 < p ^ (s + 2) := pow_pos hp.out.pos _
  have hfinite : Finite {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ (s + 2)} :=
    Nat.finite_of_card_ne_zero (by
      rw [card_lattices]
      exact (Finset.sum_pos (fun i _ => pow_pos hp.out.pos i) ⟨0, by simp⟩).ne')
  -- Split the lattices of index `p^(s+2)` by cyclicity of the quotient.
  let e := (Equiv.sumCompl (fun x : {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) //
      Λ.toAddSubgroup.index = p ^ (s + 2)} => IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ x.1.toAddSubgroup)))
  have key := Nat.card_congr e.symm
  rw [Nat.card_sum] at key
  have eCyc : Nat.card {x : {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) //
      Λ.toAddSubgroup.index = p ^ (s + 2)} // IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ x.1.toAddSubgroup)} =
      Nat.card {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ (s + 2) ∧
        IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} :=
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) => Λ.toAddSubgroup.index = p ^ (s + 2)) (fun Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) => IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)))
  have eNon : Nat.card {x : {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) //
      Λ.toAddSubgroup.index = p ^ (s + 2)} // ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ x.1.toAddSubgroup)} =
      Nat.card {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ (s + 2) ∧
        ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} :=
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) => Λ.toAddSubgroup.index = p ^ (s + 2)) (fun Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) => ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)))
  have hTotal := card_lattices p (s + 2)
  have hCyc := card_cyclic_lattices p (s + 2) (by omega)
  rw [eCyc] at key
  rw [eNon] at key
  rw [hTotal] at key
  rw [hCyc] at key
  rw [show s + 2 - 1 = s + 1 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at key
  have hs : p ^ (s + 2 - 1) = p ^ (s + 1) := by rw [show s + 2 - 1 = s + 1 by omega]
  rw [hs] at key
  omega

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
