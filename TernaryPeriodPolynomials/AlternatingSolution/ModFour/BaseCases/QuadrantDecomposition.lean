module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section


/-!
# Quadrant decomposition and the doubling endomorphism (toward Lemma 5.6, first conjunct)

Over `k = 𝔽₂`, `double := bind₁ ![X0^2, X1^2, X2]` squares the first two formal variables
`p, q` and fixes `ρ`. Composing with `evalR0` lands exactly on `evalR2`'s own substitution,
since `evalR0`'s and `evalR2`'s third slot already agree (`d7²`, not squared further) and the
first two slots square exactly as needed. Every `p : Poly2` decomposes as
`p = double A + X1 * double B + X0 * double D + X0 * X1 * double E`, by an
`MvPolynomial.induction_on` mirroring `SquaredLiftInvariance.lean`'s `mod_four_gen`. In
characteristic two, `pderiv 0` and `pderiv 1` both kill every `double T`: each generator of
`double` is either fixed by the relevant `pderiv` (cross variable, zero derivative) or squared
(same variable, derivative `2 • (-) = 0` in characteristic two).
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- Squares the formal `p, q` variables and fixes `ρ`. -/
noncomputable def double : Poly2 →ₐ[ZMod 2] Poly2 := bind₁ ![X 0 ^ 2, X 1 ^ 2, X 2]

/-- `evalR0 ∘ double = evalR2`, pointwise. -/
theorem evalR0_double (T : Poly2) : evalR0 (double T) = evalR2 T := by
  induction T using MvPolynomial.induction_on with
  | C a => simp [double, evalR0, evalR2]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    fin_cases i <;> simp [double, evalR0, evalR2, bind₁_X_right, map_pow]

/-- If `pderiv i` kills every generator of a `bind₁` substitution, it kills every image. -/
private theorem pderiv_bind₁_of_forall_eq_zero {i : Fin 3} {f : Fin 3 → Poly2}
    (hf : ∀ j, pderiv i (f j) = 0) (T : Poly2) : pderiv i (bind₁ f T) = 0 := by
  induction T using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, bind₁_X_right, MvPolynomial.pderiv_mul, hp, hf j]
    ring

private theorem ne_fin3_01 : (1 : Fin 3) ≠ 0 := by decide
private theorem ne_fin3_10 : (0 : Fin 3) ≠ 1 := by decide
private theorem ne_fin3_20 : (2 : Fin 3) ≠ 0 := by decide
private theorem ne_fin3_21 : (2 : Fin 3) ≠ 1 := by decide

/-- `pderiv 0` kills every generator of `double`. -/
private theorem pderiv0_double_gen (j : Fin 3) :
    pderiv 0 ((![X 0 ^ 2, X 1 ^ 2, X 2] : Fin 3 → Poly2) j) = 0 := by
  fin_cases j
  · show pderiv 0 (X 0 ^ 2) = 0
    rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
    simp [CharTwo.add_self_eq_zero]
  · show pderiv 0 (X 1 ^ 2) = 0
    rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne ne_fin3_01]
    ring
  · show pderiv 0 (X 2 : Poly2) = 0
    exact MvPolynomial.pderiv_X_of_ne ne_fin3_20

/-- `pderiv 1` kills every generator of `double`. -/
private theorem pderiv1_double_gen (j : Fin 3) :
    pderiv 1 ((![X 0 ^ 2, X 1 ^ 2, X 2] : Fin 3 → Poly2) j) = 0 := by
  fin_cases j
  · show pderiv 1 (X 0 ^ 2) = 0
    rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne ne_fin3_10]
    ring
  · show pderiv 1 (X 1 ^ 2) = 0
    rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
    simp [CharTwo.add_self_eq_zero]
  · show pderiv 1 (X 2 : Poly2) = 0
    exact MvPolynomial.pderiv_X_of_ne ne_fin3_21

/-- `pderiv 0` kills every `double T`. -/
theorem pderiv0_double (T : Poly2) : pderiv 0 (double T) = 0 :=
  pderiv_bind₁_of_forall_eq_zero pderiv0_double_gen T

/-- `pderiv 1` kills every `double T`. -/
theorem pderiv1_double (T : Poly2) : pderiv 1 (double T) = 0 :=
  pderiv_bind₁_of_forall_eq_zero pderiv1_double_gen T

theorem double_X0 : double (X 0) = X 0 ^ 2 := by simp [double, bind₁_X_right]
theorem double_X1 : double (X 1) = X 1 ^ 2 := by simp [double, bind₁_X_right]
theorem double_X2 : double (X 2) = X 2 := by simp [double, bind₁_X_right]

/-- **Quadrant decomposition.** Every `p : Poly2` splits as a `double`-image in each of the
four residue classes mod `(2,2)` in `(deg_{X0}, deg_{X1})`. -/
theorem exists_quadrant (p : Poly2) :
    ∃ A B D E : Poly2, p = double A + X 1 * double B + X 0 * double D + X 0 * X 1 * double E := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, 0, 0, by simp [double]⟩
  | add p q hp hq =>
    obtain ⟨Ap, Bp, Dp, Ep, hp⟩ := hp
    obtain ⟨Aq, Bq, Dq, Eq, hq⟩ := hq
    refine ⟨Ap + Aq, Bp + Bq, Dp + Dq, Ep + Eq, ?_⟩
    rw [hp, hq]
    simp only [map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨A, B, D, E, hp⟩ := hp
    fin_cases i
    · exact ⟨X 0 * D, X 0 * E, A, B, by
        rw [hp]; simp [map_mul, double_X0]; ring⟩
    · exact ⟨X 1 * B, A, X 1 * E, D, by
        rw [hp]; simp [map_mul, double_X1]; ring⟩
    · exact ⟨A * X 2, B * X 2, D * X 2, E * X 2, by
        rw [hp]; simp [map_mul, double_X2]; ring⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
