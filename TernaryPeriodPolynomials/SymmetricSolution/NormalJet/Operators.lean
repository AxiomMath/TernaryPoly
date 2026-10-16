module

public import TernaryPeriodPolynomials.SymmetricSolution.Bernoulli.Triple
public import Mathlib.RingTheory.PowerSeries.Derivative

@[expose] public section


/-!
# The operator identities behind the second normal-jet identity (MR-7)

Formalized by Claude Sonnet 5.5.  The three cancellations in the proof of equation `eq:normal-jet`:
`B(3t)(1+eᵗ+e²ᵗ) = 3B(t)` (see `BernoulliTriple`), `-B(t) + tB'(3t)(1+eᵗ+e²ᵗ) + t e²ᵗ B(3t) = -e²ᵗ B(3t) B(t)` (`bernoulli_derivative_identity`), and `B(t)(eᵗ-1) = t`.
-/

open PowerSeries

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.NormalJet

open TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section Series

theorem derivative_exp' : d⁄dX (exp ℂ) = exp ℂ := by
  ext n
  rw [coeff_derivative]
  simp only [coeff_exp]
  rw [Nat.factorial_succ]
  have hn : ((n.factorial : ℚ)) ≠ 0 := by positivity
  simp only [one_div, map_inv₀, map_natCast]
  push_cast
  field_simp

/-- `B'(t)(eᵗ - 1) + B(t) eᵗ = 1`, the derivative of `B(t)(eᵗ - 1) = t`. -/
theorem bernoulli_derivative_basic :
    d⁄dX (bernoulliPowerSeries ℂ) * (exp ℂ - 1) + bernoulliPowerSeries ℂ * exp ℂ = 1 := by
  have h := congrArg (d⁄dX) (bernoulliPowerSeries_mul_exp_sub_one ℂ)
  rw [Derivation.leibniz, map_sub, derivative_exp', derivative_one, sub_zero, derivative_X] at h
  simp only [smul_eq_mul] at h
  linear_combination h

/-- **`-B(t) + t B'(3t)(1 + eᵗ + e²ᵗ) + t e²ᵗ B(3t) = -e²ᵗ B(3t) B(t)`** in `ℂ⟦t⟧`, with `B'(3t) = rescale 3 B'`. -/
theorem bernoulli_derivative_identity :
    -bernoulliPowerSeries ℂ +
      (X * rescale (3 : ℂ) (d⁄dX (bernoulliPowerSeries ℂ))) * (1 + exp ℂ + exp ℂ * exp ℂ) +
      X * (exp ℂ * exp ℂ) * rescale (3 : ℂ) (bernoulliPowerSeries ℂ) +
      (exp ℂ * exp ℂ) * rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * bernoulliPowerSeries ℂ = 0 := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℂ
  have hexp : rescale (3 : ℂ) (exp ℂ) = exp ℂ ^ 3 := by
    have := (exp_pow_eq_rescale_exp (A := ℂ) 3).symm
    simpa using this
  have hU := congrArg (rescale (3 : ℂ)) bernoulli_derivative_basic
  rw [map_add, map_mul, map_mul, map_sub, map_one, hexp] at hU
  have hB3 := congrArg (rescale (3 : ℂ)) hB
  rw [map_mul, map_sub, map_one, hexp, rescale_X] at hB3
  have hne : exp ℂ - 1 ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    simp [coeff_exp] at this
  apply mul_right_cancel₀ hne
  rw [zero_mul]
  generalize bernoulliPowerSeries ℂ = B at *
  generalize rescale (3 : ℂ) (d⁄dX B) = U at *
  generalize rescale (3 : ℂ) B = B3 at *
  generalize exp ℂ = e at *
  linear_combination (-1 + e * e * B3) * hB + (X : ℂ⟦X⟧) * hU

end Series


section Ev

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Evaluation of a truncated power series at a nilpotent element: a ring homomorphism `ℂ⟦t⟧ → R`. -/
def evHom (D : R) {N : ℕ} (hN : 0 < N) (nil : D ^ N = 0) : ℂ⟦X⟧ →+* R where
  toFun f := Polynomial.aeval D (PowerSeries.trunc N f)
  map_one' := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    simp [PowerSeries.trunc_one]
  map_mul' := nilpotent_aeval_trunc_mul D nil
  map_zero' := by simp
  map_add' f g := by simp [map_add]

theorem evHom_apply (D : R) {N : ℕ} (hN : 0 < N) (nil : D ^ N = 0) (f : ℂ⟦X⟧) :
    evHom D hN nil f = ∑ k ∈ Finset.range N, coeff k f • D ^ k := by
  change Polynomial.aeval D (PowerSeries.trunc N f) = _
  rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [Algebra.smul_def]

theorem evHom_X (D : R) {N : ℕ} (hN : 2 ≤ N) (nil : D ^ N = 0) :
    evHom D (by omega) nil X = D := by
  change Polynomial.aeval D (PowerSeries.trunc N X) = D
  rw [PowerSeries.trunc_X_of hN, Polynomial.aeval_X]

theorem bernoulli_rescale_three_mul :
    rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (1 + exp ℂ + exp ℂ * exp ℂ) =
      C (3 : ℂ) * bernoulliPowerSeries ℂ := by
  rw [rescale_bernoulli_mul_exp, smul_eq_C_mul]

/-- **The operator identity of the second normal-jet identity.**  For a nilpotent operator `D` acting on `M`,
with `φ` evaluation of power series at `D` (so `φ B = B(D)`, `φ e = e^D = τ`), and vectors with `D h = w₃ - w₂`,
`D p = w₁ + w₂`:
`(-B + t B'(3t)(1+e+e²))h + (3B - B(3t)(1+e)) w₁ + B(3t) e² w₃ = e² B(3t) B (e p - p - h)`. -/
theorem normal_jet_operator_identity {M : Type*} [AddCommGroup M] [Module R M] (D : R) {N : ℕ}
    (hN : 2 ≤ N) (nil : D ^ N = 0) (h w1 w2 w3 p : M)
    (hDh : D • h = w3 - w2) (hDp : D • p = w1 + w2) :
    evHom D (by omega) nil (-bernoulliPowerSeries ℂ +
        (X * rescale (3 : ℂ) (d⁄dX (bernoulliPowerSeries ℂ))) * (1 + exp ℂ + exp ℂ * exp ℂ)) • h +
      evHom D (by omega) nil (C (3 : ℂ) * bernoulliPowerSeries ℂ -
        rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (1 + exp ℂ)) • w1 +
      evHom D (by omega) nil (rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (exp ℂ * exp ℂ)) • w3 =
    evHom D (by omega) nil (exp ℂ * exp ℂ * rescale (3 : ℂ) (bernoulliPowerSeries ℂ) *
        bernoulliPowerSeries ℂ) •
      (evHom D (by omega) nil (exp ℂ) • p - p - h) := by
  let _ : Module ℂ⟦X⟧ M := Module.compHom M (evHom D (by omega) nil)
  have hsmul : ∀ (f : ℂ⟦X⟧) (x : M), f • x = evHom D (by omega) nil f • x := fun _ _ => rfl
  have hX : ∀ x : M, (X : ℂ⟦X⟧) • x = D • x := by
    intro x; rw [hsmul, evHom_X D hN nil]
  have hDh' : (X : ℂ⟦X⟧) • h = w3 - w2 := by rw [hX]; exact hDh
  have hDp' : (X : ℂ⟦X⟧) • p = w1 + w2 := by rw [hX]; exact hDp
  have hw1 : w1 = (X : ℂ⟦X⟧) • p - w2 := by rw [hDp']; abel
  have hw3 : w3 = (X : ℂ⟦X⟧) • h + w2 := by rw [hDh']; abel
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℂ
  have I1 := bernoulli_rescale_three_mul
  have Sh := bernoulli_derivative_identity
  rw [← hsmul, ← hsmul, ← hsmul, ← hsmul]
  rw [hw1, hw3]
  generalize hAh : (-bernoulliPowerSeries ℂ +
        (X * rescale (3 : ℂ) (d⁄dX (bernoulliPowerSeries ℂ))) * (1 + exp ℂ + exp ℂ * exp ℂ)) = Ah
  generalize hA1 : (C (3 : ℂ) * bernoulliPowerSeries ℂ -
        rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (1 + exp ℂ)) = A1
  generalize hA3 : (rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (exp ℂ * exp ℂ)) = A3
  generalize hRr : (exp ℂ * exp ℂ * rescale (3 : ℂ) (bernoulliPowerSeries ℂ) *
        bernoulliPowerSeries ℂ) = Rr
  have c_h : Ah + A3 * X = -Rr := by
    rw [← hAh, ← hA3, ← hRr]
    linear_combination Sh
  have c_p : A1 * X = Rr * exp ℂ - Rr := by
    rw [← hA1, ← hRr]
    linear_combination (-(X : ℂ⟦X⟧)) * I1 + (-(exp ℂ * exp ℂ * rescale (3 : ℂ) (bernoulliPowerSeries ℂ))) * hB
  have c_w : A3 - A1 = 0 := by
    rw [← hA3, ← hA1]
    linear_combination I1
  calc Ah • h + A1 • ((X : ℂ⟦X⟧) • p - w2) + A3 • ((X : ℂ⟦X⟧) • h + w2)
      = (Ah + A3 * X) • h + (A1 * X) • p + (A3 - A1) • w2 := by
        simp only [smul_sub, smul_add, smul_smul, add_smul, sub_smul]; abel
    _ = (-Rr) • h + (Rr * exp ℂ - Rr) • p := by rw [c_h, c_p, c_w, zero_smul, add_zero]
    _ = Rr • (exp ℂ • p - p - h) := by
        simp only [smul_sub, smul_smul, neg_smul, sub_smul]; abel

end Ev

end TernaryPeriodPolynomials.Argument.Identities.NormalJet
