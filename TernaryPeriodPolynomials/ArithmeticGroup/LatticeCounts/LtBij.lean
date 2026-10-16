module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtSurj

@[expose] public section


/-!
# The bijection `t ↦ L_t` from `cyclicHNF p s` onto the cyclic index-`p^s` lattices

Formalized by Claude Haiku 5.5.

Injectivity is `hermLat_inj` (`LtInj`), surjectivity is `exists_cyclicHNF_hermLat` (`LtSurj`),
and the image lies in the stated lattice class by `hermLat_index_cyclic` (`LtDictionary`).
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The bijection.** `t ↦ hermLat p t` is a bijection from the cyclic Hermite triples of level
`p^s` onto the `ℤ_p`-lattices of index `p^s` with cyclic quotient. -/
noncomputable def cyclicHNFEquiv (s : ℕ) :
    {t // t ∈ TernaryPeriodPolynomials.Argument.LatticeCounts.cyclicHNF p s} ≃
      {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) //
        Λ.toAddSubgroup.index = p ^ s ∧ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} :=
  Equiv.ofBijective
    (fun t => ⟨hermLat p t.1, hermLat_index_cyclic t.2⟩)
    (by
      constructor
      · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
        have h' : hermLat p t = hermLat p t' := congrArg Subtype.val h
        have hm : t ∈ TernaryPeriodPolynomials.Argument.LatticeCounts.hnfData (p ^ s) :=
          (Finset.mem_filter.1 ht).1
        have hm' : t' ∈ TernaryPeriodPolynomials.Argument.LatticeCounts.hnfData (p ^ s) :=
          (Finset.mem_filter.1 ht').1
        exact Subtype.ext (hermLat_inj hm hm' h')
      · rintro ⟨Λ, hΛ, hc⟩
        obtain ⟨t, ht, hL⟩ := exists_cyclicHNF_hermLat hΛ hc
        exact ⟨⟨t, ht⟩, Subtype.ext hL⟩)

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
