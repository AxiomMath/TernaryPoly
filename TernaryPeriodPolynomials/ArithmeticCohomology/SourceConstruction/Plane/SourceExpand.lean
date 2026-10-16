module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.PolyExpansion

@[expose] public section


/-!
# Monomial expansion of binary forms

A binary form of degree `k` is the finite sum of its degree-`k` monomials with its coefficients, so
a linear map out of the binary forms is determined by its values on the monomials, with the
coefficients of the argument as scalars. This turns a coordinatewise statement about the binary
coefficients of a cuspidal Levi cocycle into a statement about the polynomial values of the plane
source cocycle.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein MvPolynomial

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The finite set of exponent vectors of total degree `k` in two variables. -/
def binaryMonomials (k : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (Finsupp.finite_of_degree_eq (σ := Fin 2) k).toFinset

theorem mem_binaryMonomials {k : ℕ} {d : Fin 2 →₀ ℕ} :
    d ∈ binaryMonomials k ↔ Finsupp.degree d = k :=
  Set.Finite.mem_toFinset _

theorem support_subset_binaryMonomials {k : ℕ} (w : Binary.HomogeneousPoly k) :
    w.val.support ⊆ binaryMonomials k := by
  intro d hd
  rw [mem_binaryMonomials]
  have hmem : w.val ∈ AddMonoidAlgebra.supported ℂ ℂ {d | Finsupp.degree d = k} := by
    rw [← MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact w.property
  exact (AddMonoidAlgebra.mem_supported.mp hmem) hd

/-- The monomial `x^ν`, projected to the degree-`k` component of the binary forms. -/
def binaryMono (k : ℕ) (ν : Fin 2 →₀ ℕ) : Binary.HomogeneousPoly k :=
  ⟨MvPolynomial.homogeneousComponent k (MvPolynomial.monomial ν (1 : ℂ)),
    MvPolynomial.homogeneousComponent_mem k _⟩

/-- **Monomial expansion of a binary form.** -/
theorem binary_expand {k : ℕ} (Q : Binary.HomogeneousPoly k) :
    Q = ∑ ν ∈ binaryMonomials k, Q.val.coeff ν • binaryMono k ν := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, binaryMono]
  have hQ : MvPolynomial.homogeneousComponent k Q.val = Q.val := by
    rw [MvPolynomial.homogeneousComponent_of_mem Q.property, ite_eq_left rfl]
  conv_lhs => rw [← hQ, MvPolynomial.as_sum Q.val]
  rw [map_sum]
  rw [Finset.sum_subset (support_subset_binaryMonomials Q) (fun d _ hdS => by
    have h0 : Q.val.coeff d = 0 := Finsupp.notMem_support_iff.mp hdS
    simp [h0])]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hmon : MvPolynomial.monomial d (Q.val.coeff d) =
      Q.val.coeff d • MvPolynomial.monomial d (1 : ℂ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul]

/-- A linear map out of the binary forms of degree `k` is its coefficient-weighted sum of values on
the monomials. -/
theorem binary_linear_apply_eq_sum {W : Type*} [AddCommGroup W] [Module ℂ W] {k : ℕ}
    (T : Binary.HomogeneousPoly k →ₗ[ℂ] W) (Q : Binary.HomogeneousPoly k) :
    T Q = ∑ ν ∈ binaryMonomials k, Q.val.coeff ν • T (binaryMono k ν) := by
  conv_lhs => rw [binary_expand Q]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun ν _ => by rw [map_smul])

/-- A coefficient of the image of a binary form under a linear map to ternary forms. -/
theorem binary_coeff_apply_eq_sum {k m : ℕ} (T : Binary.HomogeneousPoly k →ₗ[ℂ] HomogeneousPoly m)
    (Q : Binary.HomogeneousPoly k) (μ : Fin 3 →₀ ℕ) :
    (T Q).val.coeff μ =
      ∑ ν ∈ binaryMonomials k, Q.val.coeff ν * (T (binaryMono k ν)).val.coeff μ := by
  rw [binary_linear_apply_eq_sum T Q, Submodule.coe_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]

end TernaryPeriodPolynomials.SourceConstruction
