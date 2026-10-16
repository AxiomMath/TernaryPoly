module

public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-!
# The coefficient condition alone does not imply vanishing

Formalized by Claude Haiku 5.5.

The paper states: "The coefficient condition alone does not imply vanishing": for some `d`
there is a nonzero `q ∈ 𝓑_d` with `[XY^{d-1}] q = 0`. Here `𝓑_d = 𝓑_d^+` is the space of
`eq:signed-binary` with `ε = +1`:
`q(Y,X) = q(X,Y)`, `q(-X,Y) = q(X,-Y) = -q(X,Y)`, `q(X,0) = q(0,Y) = 0`, `N₂q = 0`, where
`N₂q = q(X,Y) + q(-Y,X-Y) + q(Y-X,-X)`, and `q` is homogeneous of degree `d`.

The statement below writes these conditions literally, with the substitutions of
`Revision/Defs/Polynomial.lean`, for `d = 22` over `ℚ`. The witness is explicit, with integer
coefficients (the basis vector of `𝓑_22` with `XY²¹`-coefficient zero, scaled by `144`):

  q = 144X³Y¹⁹ − 1400X⁵Y¹⁷ + 5349X⁷Y¹⁵ − 11100X⁹Y¹³ + 14014X¹¹Y¹¹
      − 11100X¹³Y⁹ + 5349X¹⁵Y⁷ − 1400X¹⁷Y⁵ + 144X¹⁹Y³.

It is the basis vector of the two-dimensional space `𝓑_22` (dimension `dim S_24 = 2`) that has no
`XY²¹` term. Degrees `d ∈ {10, 14, …, 20, 24}` (where `𝓑_d` is one-dimensional with a nonzero
`XY^{d-1}` coefficient) and `d = 12` (where `𝓑_d = 0`) give no witness; `d = 22` is the least
degree with a witness.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

/-- The explicit degree-22 element `q` of `𝓑_22` with vanishing `XY²¹` coefficient, with integer
coefficients (`144` times the basis vector with rational coefficients `1, −175/18, 1783/48, …`).
The coefficients are listed by the exponent `a` of `X` in `X^a Y^(22-a)`. -/
def coefficientWitness22 : MvPolynomial (Fin 2) ℚ :=
  C (144 : ℚ) * X 0 ^ 3 * X 1 ^ 19 + C (-1400 : ℚ) * X 0 ^ 5 * X 1 ^ 17 +
    C (5349 : ℚ) * X 0 ^ 7 * X 1 ^ 15 + C (-11100 : ℚ) * X 0 ^ 9 * X 1 ^ 13 +
    C (14014 : ℚ) * X 0 ^ 11 * X 1 ^ 11 + C (-11100 : ℚ) * X 0 ^ 13 * X 1 ^ 9 +
    C (5349 : ℚ) * X 0 ^ 15 * X 1 ^ 7 + C (-1400 : ℚ) * X 0 ^ 17 * X 1 ^ 5 +
    C (144 : ℚ) * X 0 ^ 19 * X 1 ^ 3

/-- Each monomial term of `coefficientWitness22` has total degree `22`. -/
theorem term_isHomogeneous (c : ℚ) (a b : ℕ) (h : a + b = 22) :
    (C c * X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℚ).IsHomogeneous 22 := by
  have := ((isHomogeneous_C (σ := Fin 2) (R := ℚ) c).mul
    ((isHomogeneous_X ℚ (0 : Fin 2)).pow a)).mul ((isHomogeneous_X ℚ (1 : Fin 2)).pow b)
  convert this using 1
  simp only [zero_add]
  omega

theorem coefficientWitness22_isHomogeneous : coefficientWitness22.IsHomogeneous 22 := by
  unfold coefficientWitness22
  repeat' apply IsHomogeneous.add
  all_goals (apply term_isHomogeneous; norm_num)

/-- A monomial term `c X^a Y^b` as a `MvPolynomial.monomial`. -/
theorem term_eq_monomial (c : ℚ) (a b : ℕ) :
    (C c * X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℚ) =
      monomial (Finsupp.single 0 a + Finsupp.single 1 b) c := by
  simp [X_pow_eq_monomial, C_mul_monomial]

/-- Two exponent vectors `a e₀ + b e₁` agree iff their entries agree. -/
theorem witness_single_add_eq_iff (a b c d : ℕ) :
    (Finsupp.single 0 a + Finsupp.single 1 b : Fin 2 →₀ ℕ) =
      Finsupp.single 0 c + Finsupp.single 1 d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The `XY²¹` coefficient of `coefficientWitness22` vanishes: its monomials have `X`-exponents
`3, 5, …, 19`, none equal to `1`. -/
theorem coefficientWitness22_coeff_XY21 :
    coefficientWitness22.coeff (Finsupp.single 0 1 + Finsupp.single 1 21) = 0 := by
  unfold coefficientWitness22
  simp only [term_eq_monomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_monomial,
    witness_single_add_eq_iff]
  norm_num

/-- The witness is nonzero: its `X³Y¹⁹` coefficient is `1`. -/
theorem coefficientWitness22_ne_zero : coefficientWitness22 ≠ 0 := by
  intro h
  have h3 := congrArg (·.coeff (Finsupp.single 0 3 + Finsupp.single 1 19)) h
  unfold coefficientWitness22 at h3
  simp only [term_eq_monomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_monomial,
    witness_single_add_eq_iff, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
  norm_num at h3

/-- **Coefficient condition does not imply vanishing**. There is a
homogeneous `q` of degree `22` in `ℚ[X,Y]` satisfying the literal conditions of `𝓑_22 = 𝓑_22^+`
(`eq:signed-binary`, `ε = +1`: swap symmetry, oddness in each variable, the axis conditions and
`N₂q = 0`), whose coefficient of `X¹Y²¹ = X Y^{d-1}` is zero, and which is nonzero. -/
theorem coefficient_condition_not_sufficient :
    ∃ q : MvPolynomial (Fin 2) ℚ, q.IsHomogeneous 22 ∧
      bind₁ ![X 1, X 0] q = q ∧
      bind₁ ![-X 0, X 1] q = -q ∧
      bind₁ ![X 0, -X 1] q = -q ∧
      bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0 ∧
      bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0 ∧
      q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0 ∧
      q.coeff (Finsupp.single 0 1 + Finsupp.single 1 21) = 0 ∧
      q ≠ 0 := by
  refine ⟨coefficientWitness22, coefficientWitness22_isHomogeneous, ?_, ?_, ?_, ?_, ?_, ?_,
    coefficientWitness22_coeff_XY21, coefficientWitness22_ne_zero⟩
  all_goals (unfold coefficientWitness22; simp [map_ofNat]; try ring)

end TernaryPeriodPolynomials.Argument.Identities
