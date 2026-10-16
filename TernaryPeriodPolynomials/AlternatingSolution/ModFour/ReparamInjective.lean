module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section



/-! Injectivity of the coefficient reparametrisation `(p, q, ρ) ↦ (p, q, ρ²)` used in the
proof of Theorem 5.2 (`mf:thm:main`), step `mf:lem:cancellation`: `evalR0` factors as
`invariantEval ∘ reparam`, and `reparam` is injective since on monomials it acts by the
injective exponent rescaling `(d₀, d₁, d₂) ↦ (d₀, d₁, 2 d₂)`. -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- The substitution `(X 0, X 1, X 2) ↦ (X 0, X 1, X 2 ^ 2)` on formal polynomials in
`p, q, ρ`. Composing with `invariantEval` recovers `evalR0`. -/
noncomputable def reparam : Poly2 →ₐ[ZMod 2] Poly2 :=
  bind₁ ![X 0, X 1, X 2 ^ 2]

/-- The per-coordinate exponent scale factors matching `reparam` on monomials. -/
def scale : Fin 3 → ℕ := ![1, 1, 2]

private theorem scale_pos (i : Fin 3) : 0 < scale i := by
  fin_cases i <;> decide

/-- The exponent rescaling `d ↦ (d 0, d 1, 2 * d 2)` induced by `reparam`. -/
noncomputable def expScale (d : Fin 3 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => scale i * d i)

private theorem expScale_apply (d : Fin 3 →₀ ℕ) (i : Fin 3) :
    expScale d i = scale i * d i := by
  simp [expScale]

private theorem expScale_injective : Function.Injective expScale := by
  intro d₁ d₂ h
  have h' : (fun i => scale i * d₁ i) = (fun i => scale i * d₂ i) :=
    Finsupp.equivFunOnFinite.symm.injective h
  apply Finsupp.ext
  intro i
  exact Nat.eq_of_mul_eq_mul_left (scale_pos i) (congrFun h' i)

/-- A `Fin 3`-indexed product of powers over the support of an exponent vector equals the
product over all of `Fin 3`, since the missing terms are `_ ^ 0 = 1`. -/
private theorem prod_support_eq_prod_univ {M : Type*} [CommMonoid M] (d : Fin 3 →₀ ℕ)
    (g : Fin 3 → M) : ∏ i ∈ d.support, g i ^ d i = ∏ i : Fin 3, g i ^ d i := by
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hd0 : d i = 0 := by
    by_contra hne
    exact hi (Finsupp.mem_support_iff.mpr hne)
  rw [hd0, pow_zero]

/-- `reparam` sends the monomial `X^d` with coefficient `r` to the monomial `X^(expScale d)`
with the same coefficient. -/
theorem reparam_monomial (d : Fin 3 →₀ ℕ) (r : ZMod 2) :
    reparam (monomial d r) = monomial (expScale d) r := by
  have hL : reparam (monomial d r) = C r * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ (2 * d 2)) := by
    show bind₁ ![X 0, X 1, X 2 ^ 2] (monomial d r) = _
    rw [bind₁_monomial, prod_support_eq_prod_univ d, Fin.prod_univ_three]
    simp [pow_mul]
  have hR : monomial (expScale d) r = C r * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ (2 * d 2)) := by
    rw [monomial_eq]
    have hprod : ((expScale d).prod (fun n e => X n ^ e) : Poly2)
        = ∏ i ∈ (expScale d).support, X i ^ (expScale d) i := rfl
    rw [hprod, prod_support_eq_prod_univ (expScale d), Fin.prod_univ_three]
    simp [expScale_apply, scale]
  rw [hL, hR]

/-- `reparam` has trivial kernel. -/
theorem reparam_eq_zero {h : Poly2} (hh : reparam h = 0) : h = 0 := by
  have hz : ∀ d ∈ h.support, h.coeff d = 0 := by
    intro d hd
    have hcoeff : (reparam h).coeff (expScale d) = h.coeff d := by
      conv_lhs => rw [← support_sum_monomial_coeff h, map_sum]
      rw [coeff_sum]
      simp only [reparam_monomial, coeff_monomial, expScale_injective.eq_iff]
      rw [Finset.sum_ite_eq' h.support d (h.coeff ·), ite_eq_left hd]
    rw [← hcoeff, hh]
    simp
  calc h = ∑ d ∈ h.support, monomial d (h.coeff d) := (support_sum_monomial_coeff h).symm
    _ = ∑ d ∈ h.support, monomial d 0 := Finset.sum_congr rfl (fun d hd => by rw [hz d hd])
    _ = 0 := by simp

/-- `reparam` is injective. -/
theorem reparam_injective : Function.Injective reparam :=
  (injective_iff_map_eq_zero reparam).mpr fun _ ha => reparam_eq_zero ha

end TernaryPeriodPolynomials.Argument
