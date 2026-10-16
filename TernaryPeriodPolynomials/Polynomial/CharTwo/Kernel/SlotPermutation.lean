module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.ProjectorKAll
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

@[expose] public section





open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

variable {g : Poly2}

/-- Public restatement of the characteristic-2 numeral-reduction fact.

-/
theorem ofNat_mod2' (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly2) = ((n % 2 : ℕ) : Poly2) :=
  CharP.cast_eq_mod Poly2 2 n

/-- Substituting a symmetric polynomial through any slot vector `ν` is unchanged if `ν` is
first permuted by `τ` (precomposed): the permutation can be absorbed via `rename`. -/
theorem slot_perm_eq (hg : g.IsSymmetric) (ν : Fin 3 → Poly2) (τ : Equiv.Perm (Fin 3)) :
    bind₁ (ν ∘ ⇑τ) g = bind₁ ν g := by
  rw [← MvPolynomial.bind₁_rename ν τ g, hg τ]

/-- General pairing helper: if `μ` agrees with `ν ∘ τ` componentwise (for some permutation `τ`
of the three slots), then substituting a symmetric `g` through `μ` or `ν` gives the same
result. The componentwise hypothesis is proved by `ring`-closed small computations, so no
assumption is made about the surface syntax `μ`, `ν` happen to be written in. -/
theorem vec_perm_bind (hg : g.IsSymmetric) (μ ν : Fin 3 → Poly2) (τ : Equiv.Perm (Fin 3))
    (hcomp : ∀ i : Fin 3, μ i = ν (τ i)) :
    bind₁ μ g = bind₁ ν g := by
  have hμν : μ = ν ∘ ⇑τ := funext hcomp
  rw [hμν]
  exact slot_perm_eq hg ν τ

end TernaryPeriodPolynomials.Argument.CharTwoKernel
