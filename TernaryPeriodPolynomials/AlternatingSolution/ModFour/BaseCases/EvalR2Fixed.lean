module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators

@[expose] public section



/-! `evalR2 h` is fixed by both norm substitutions `sub₁`/`sub₂`, for any `h`. Direct analogue of
`TernaryPeriodPolynomials.Argument.evalR0_sub1_fixed`/`evalR0_sub2_fixed`
(`ModFourMain/ExpandOddNormZero.lean`), substituting the vector `![d4 ^ 2, d6 ^ 2, d7 ^ 2]` for
`![d4, d6, d7 ^ 2]`. Needed to show `evalSquaredLift P * baseSym j m` has even `threeTermNorm`,
for `modFour_beta_triangular`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem evalR2_C (x : ZMod 2) : evalR2 (MvPolynomial.C x) = MvPolynomial.C x := by
  show bind₁ ![d4 ^ 2, d6 ^ 2, d7 ^ 2] (C x) = C x
  exact bind₁_C_right _ _

private theorem evalR2_X (n : Fin 3) :
    evalR2 (X n) = (![d4 ^ 2, d6 ^ 2, d7 ^ 2] : Fin 3 → Poly2) n := by
  show bind₁ ![d4 ^ 2, d6 ^ 2, d7 ^ 2] (X n) = _
  exact bind₁_X_right _ _

private theorem evalR2_add' (p q : Poly2) : evalR2 (p + q) = evalR2 p + evalR2 q :=
  map_add evalR2 p q

private theorem evalR2_mul' (p q : Poly2) : evalR2 (p * q) = evalR2 p * evalR2 q :=
  map_mul evalR2 p q


theorem sub1_d4' : sub₁ d4 = d4 := by simpa [invariant] using sub₁_invariant 0
theorem sub1_d6' : sub₁ d6 = d6 := by simpa [invariant] using sub₁_invariant 1
theorem sub1_d7' : sub₁ d7 = d7 := by simpa [invariant] using sub₁_invariant 2
theorem sub2_d4' : sub₂ d4 = d4 := by simpa [invariant] using sub₂_invariant 0
theorem sub2_d6' : sub₂ d6 = d6 := by simpa [invariant] using sub₂_invariant 1
theorem sub2_d7' : sub₂ d7 = d7 := by simpa [invariant] using sub₂_invariant 2

private theorem evalR2_X_sub1_fixed (n : Fin 3) : sub₁ (evalR2 (X n)) = evalR2 (X n) := by
  fin_cases n <;> simp [evalR2_X, sub1_d4', sub1_d6', map_pow, sub1_d7']

private theorem evalR2_X_sub2_fixed (n : Fin 3) : sub₂ (evalR2 (X n)) = evalR2 (X n) := by
  fin_cases n <;> simp [evalR2_X, sub2_d4', sub2_d6', map_pow, sub2_d7']

/-- `evalR2 h` is fixed by the first norm substitution, for any `h`. -/
theorem evalR2_sub1_fixed (h : Poly2) : sub₁ (evalR2 h) = evalR2 h := by
  induction h using MvPolynomial.induction_on with
  | C a => rw [evalR2_C]; show bind₁ ![X 1, X 0 + X 1, X 2] (C a) = C a; exact bind₁_C_right _ _
  | add p q hp hq => rw [evalR2_add', map_add, hp, hq]
  | mul_X p n hp => rw [evalR2_mul', map_mul, hp, evalR2_X_sub1_fixed n]

/-- `evalR2 h` is fixed by the second norm substitution, for any `h`. -/
theorem evalR2_sub2_fixed (h : Poly2) : sub₂ (evalR2 h) = evalR2 h := by
  induction h using MvPolynomial.induction_on with
  | C a => rw [evalR2_C]; show bind₁ ![X 0 + X 1, X 0, X 2] (C a) = C a; exact bind₁_C_right _ _
  | add p q hp hq => rw [evalR2_add', map_add, hp, hq]
  | mul_X p n hp => rw [evalR2_mul', map_mul, hp, evalR2_X_sub2_fixed n]

end TernaryPeriodPolynomials.Argument.ModFourBeta
