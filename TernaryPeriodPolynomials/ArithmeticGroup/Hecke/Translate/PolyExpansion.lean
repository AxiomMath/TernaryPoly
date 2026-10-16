/-
  The finite-degree monomial expansion used to transport coefficientwise
  properties through the coefficient representation `ρ(g)`.

  For a homogeneous polynomial `w` of degree `n`, the support of `w` is contained
  in the (finite) set of exponents of total degree `n`, so every linear
  functional on `HomogeneousPoly n` is a fixed finite linear combination of the
  coordinate functionals `MvPolynomial.coeff d` (`d` of total degree `n`).  This
  is exactly the expansion needed to reduce the `IsInduced` smoothness /
  `cuspFunctions` clauses for `ρ(g)(w)` to those for `w`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein
open MvPolynomial


noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.PolyExpansion

/-- The (finite) set of exponent vectors of total degree `n` in three variables. -/
def degreeMonomials (n : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (Finsupp.finite_of_degree_eq (σ := Fin 3) n).toFinset

theorem mem_degreeMonomials {n : ℕ} {d : Fin 3 →₀ ℕ} :
    d ∈ degreeMonomials n ↔ Finsupp.degree d = n :=
  Set.Finite.mem_toFinset _

/-- The support of a homogeneous polynomial of degree `n` is contained in
`degreeMonomials n`. -/
theorem support_subset_degreeMonomials {n : ℕ} (w : HomogeneousPoly n) :
    w.val.support ⊆ degreeMonomials n := by
  intro d hd
  rw [mem_degreeMonomials]
  have hmem : w.val ∈ AddMonoidAlgebra.supported ℂ ℂ {d | Finsupp.degree d = n} := by
    rw [← MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact w.property
  exact (AddMonoidAlgebra.mem_supported.mp hmem) hd

/-- **Monomial expansion.**  A homogeneous polynomial of degree `n` is the sum of
its degree-`n` monomials with their coefficients. -/
theorem homogeneous_eq_sum_monomials {n : ℕ} (w : HomogeneousPoly n) :
    w.val = ∑ d ∈ degreeMonomials n, MvPolynomial.monomial d (w.val.coeff d) := by
  conv_lhs => rw [MvPolynomial.as_sum w.val]
  apply Finset.sum_subset
  · exact support_subset_degreeMonomials w
  · intro d _ hdS
    have h0 : w.val.coeff d = 0 := Finsupp.notMem_support_iff.mp hdS
    simp [h0]

/-- **Linear-functional expansion.**  Any linear functional on `Poly` evaluated on
a homogeneous polynomial of degree `n` is a fixed finite linear combination of
the values on the degree-`n` monomials, with the coefficients of the polynomial
as scalars.  This is the transport lemma that reduces coefficientwise properties
of `ρ(g)(w)` to those of `w`. -/
theorem linear_apply_eq_sum (L : Poly →ₗ[ℂ] ℂ) {n : ℕ} (w : HomogeneousPoly n) :
    L w.val = ∑ d ∈ degreeMonomials n,
      w.val.coeff d * L (MvPolynomial.monomial d 1) := by
  conv_lhs => rw [MvPolynomial.as_sum w.val]
  rw [map_sum]
  rw [Finset.sum_subset (support_subset_degreeMonomials w) (fun d _ hdS => by
    have h0 : w.val.coeff d = 0 := Finsupp.notMem_support_iff.mp hdS
    simp [h0])]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hmon : MvPolynomial.monomial d (w.val.coeff d)
      = w.val.coeff d • MvPolynomial.monomial d 1 := by
    rw [show MvPolynomial.monomial d (w.val.coeff d)
        = MvPolynomial.monomial d ((w.val.coeff d) • (1 : ℂ)) from by
          rw [smul_eq_mul, mul_one]]
    rw [map_smul]
  rw [hmon, map_smul, smul_eq_mul]

end TernaryPeriodPolynomials.HeckeTranslate.PolyExpansion

end
