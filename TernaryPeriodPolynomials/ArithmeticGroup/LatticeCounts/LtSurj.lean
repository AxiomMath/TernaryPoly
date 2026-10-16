module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtInj
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Noncyclic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Surjective
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicZp

@[expose] public section


/-!
# Surjectivity of `t ↦ L_t` onto the cyclic index-`p^s` lattices

Formalized by Claude Haiku 5.5.

For a cyclic `ℤ_p`-lattice `Λ ⊆ ℤ_p²` of index `p^s`, the integral part `zPart Λ` has index `p^s`,
so it is `latOf t` for some Hermite triple `t` of level `p^s` (`hnfEquiv` is surjective).
Then `L_t = latOfZ (latOf t) = Λ`. If all entries of `Mz t` lay in `(p)`, every point of `L_t`
would lie in `pℤ_p²`, making the quotient non-cyclic; so `t` is cyclic.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp
  (Mz mulLin mulLin_apply range_mulLin_Mz_eq)
open TernaryPeriodPolynomials.Argument.LatticeCounts (hnfData cyclicHNF mem_hnfData)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicZp (mem_cyclicHNF_iff)

variable {p : ℕ} [hp : Fact p.Prime]

/-- If every entry of `Mz t` lies in `(p)`, then every point of `L_t` lies in `pℤ_p²`. -/
theorem hermLat_le_of_entries {t : ℕ × ℕ × ℕ}
    (hall : ∀ i j, Mz (q := p) t i j ∈ Ideal.span {(p : ℤ_[p])}) :
    ∀ v ∈ (hermLat p t).toAddSubgroup, (p : ℤ_[p]) ∣ v.1 ∧ (p : ℤ_[p]) ∣ v.2 := by
  intro v hv
  rw [Submodule.mem_toAddSubgroup, hermLat, LinearMap.mem_range] at hv
  obtain ⟨x, rfl⟩ := hv
  have hd : ∀ i j, (p : ℤ_[p]) ∣ Mz (q := p) t i j := fun i j =>
    Ideal.mem_span_singleton.1 (hall i j)
  rw [mulLin_apply]
  exact ⟨dvd_add ((hd 0 0).mul_right _) ((hd 0 1).mul_right _),
    dvd_add ((hd 1 0).mul_right _) ((hd 1 1).mul_right _)⟩

/-- **Surjectivity.** Every cyclic `ℤ_p`-lattice of index `p^s` is `L_t` for some
`t ∈ cyclicHNF p s`. -/
theorem exists_cyclicHNF_hermLat {s : ℕ} {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])}
    (hΛ : Λ.toAddSubgroup.index = p ^ s)
    (hc : IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)) :
    ∃ t ∈ cyclicHNF p s, hermLat p t = Λ := by
  have hn : 0 < p ^ s := pow_pos hp.out.pos s
  obtain ⟨⟨t, ht⟩, hteq⟩ :=
    (hnfEquiv hn).surjective ⟨zPart Λ.toAddSubgroup, index_zPart hΛ⟩
  have hlat : latOf t = zPart Λ.toAddSubgroup := congrArg Subtype.val hteq
  have hL : hermLat p t = Λ := by
    rw [hermLat, range_mulLin_Mz_eq (q := p) t ht, hlat, latOfZ_zPart hΛ]
  refine ⟨t, ?_, hL⟩
  rw [mem_cyclicHNF_iff (q := p) (r := s) hp.out t ht]
  intro hall
  refine not_isAddCyclic_of_le (hermLat_le_of_entries hall) ?_
  rw [hL]
  exact hc

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
