module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators

@[expose] public section



/-! `expandOdd r` always has zero reduced norm, for any `r : Fin 8 → MvPolynomial (Fin 3)
(ZMod 2)`. Used in the proof of Theorem 5.2 (`mf:thm:main`): the `piOperator (reduceTwo g) = 0`
consequence of `modFour_beta_triangular` forces `expandOdd (r + uOperator r) = 0`, and more generally every
value of `expandOdd` lies in the kernel of `TernaryPoly.CharTwoNorm.norm`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument

private theorem evalR0_C (x : ZMod 2) : evalR0 (MvPolynomial.C x) = MvPolynomial.C x := by
  show bind₁ ![d4, d6, d7 ^ 2] (C x) = C x
  exact bind₁_C_right _ _

private theorem evalR0_X (n : Fin 3) :
    evalR0 (X n) = (![d4, d6, d7 ^ 2] : Fin 3 → Poly2) n := by
  show bind₁ ![d4, d6, d7 ^ 2] (X n) = _
  exact bind₁_X_right _ _

private theorem evalR0_add' (p q : Poly2) : evalR0 (p + q) = evalR0 p + evalR0 q :=
  map_add evalR0 p q

private theorem evalR0_mul' (p q : Poly2) : evalR0 (p * q) = evalR0 p * evalR0 q :=
  map_mul evalR0 p q

private theorem sub1_d4 : sub₁ d4 = d4 := by simpa [invariant] using sub₁_invariant 0
private theorem sub1_d6 : sub₁ d6 = d6 := by simpa [invariant] using sub₁_invariant 1
private theorem sub1_d7 : sub₁ d7 = d7 := by simpa [invariant] using sub₁_invariant 2
private theorem sub2_d4 : sub₂ d4 = d4 := by simpa [invariant] using sub₂_invariant 0
private theorem sub2_d6 : sub₂ d6 = d6 := by simpa [invariant] using sub₂_invariant 1
private theorem sub2_d7 : sub₂ d7 = d7 := by simpa [invariant] using sub₂_invariant 2

private theorem evalR0_X_sub1_fixed (n : Fin 3) : sub₁ (evalR0 (X n)) = evalR0 (X n) := by
  fin_cases n <;> simp [evalR0_X, sub1_d4, sub1_d6, map_pow, sub1_d7]

private theorem evalR0_X_sub2_fixed (n : Fin 3) : sub₂ (evalR0 (X n)) = evalR0 (X n) := by
  fin_cases n <;> simp [evalR0_X, sub2_d4, sub2_d6, map_pow, sub2_d7]

/-- `evalR0 h` is fixed by the first norm substitution, for any `h`. -/
theorem evalR0_sub1_fixed (h : Poly2) : sub₁ (evalR0 h) = evalR0 h := by
  induction h using MvPolynomial.induction_on with
  | C a => rw [evalR0_C]; show bind₁ ![X 1, X 0 + X 1, X 2] (C a) = C a; exact bind₁_C_right _ _
  | add p q hp hq => rw [evalR0_add', map_add, hp, hq]
  | mul_X p n hp => rw [evalR0_mul', map_mul, hp, evalR0_X_sub1_fixed n]

/-- `evalR0 h` is fixed by the second norm substitution, for any `h`. -/
theorem evalR0_sub2_fixed (h : Poly2) : sub₂ (evalR0 h) = evalR0 h := by
  induction h using MvPolynomial.induction_on with
  | C a => rw [evalR0_C]; show bind₁ ![X 0 + X 1, X 0, X 2] (C a) = C a; exact bind₁_C_right _ _
  | add p q hp hq => rw [evalR0_add', map_add, hp, hq]
  | mul_X p n hp => rw [evalR0_mul', map_mul, hp, evalR0_X_sub2_fixed n]

/-- Multiplying by a norm-invariant element commutes with `norm`. -/
theorem norm_mul_invariant {x y : Poly2} (hx1 : sub₁ x = x) (hx2 : sub₂ x = x) :
    norm (x * y) = x * norm y := by
  show x * y + sub₁ (x * y) + sub₂ (x * y) = x * (y + sub₁ y + sub₂ y)
  rw [map_mul, map_mul, hx1, hx2]
  ring

/-- Every odd generator already lies in the kernel of `norm`. -/
theorem oddGenerator_norm_zero (j : Fin 8) : norm (oddGenerator j) = 0 := by
  show norm (generator j * d7 ^ kappa j) = 0
  rw [mul_comm]
  have hx1 : sub₁ (d7 ^ kappa j : Poly2) = d7 ^ kappa j := by rw [map_pow, sub1_d7]
  have hx2 : sub₂ (d7 ^ kappa j : Poly2) = d7 ^ kappa j := by rw [map_pow, sub2_d7]
  rw [norm_mul_invariant hx1 hx2, norm_generator j, mul_zero]

private theorem norm_sum {ι : Type*} (s : Finset ι) (F : ι → Poly2) :
    norm (∑ j ∈ s, F j) = ∑ j ∈ s, norm (F j) := by
  simp only [norm, map_sum, Finset.sum_add_distrib]

/-- `expandOdd r` always has zero reduced norm, for any `r`. -/
theorem expandOdd_norm_zero (r : Fin 8 → Poly2) : norm (expandOdd r) = 0 := by
  show norm (∑ j, evalR0 (r j) * oddGenerator j) = 0
  rw [norm_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [norm_mul_invariant (evalR0_sub1_fixed (r j)) (evalR0_sub2_fixed (r j)),
    oddGenerator_norm_zero j, mul_zero]

end TernaryPeriodPolynomials.Argument
