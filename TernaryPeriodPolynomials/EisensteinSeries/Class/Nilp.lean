module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Trans
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

@[expose] public section


/-!
# Unipotence of the coefficient transport

Paper: "the polynomial
coefficient representation is unipotent on `𝒩_R`".

`trL_sub_one_isNilpotent`: `ρ(t_v) - 1` is nilpotent on `Coef n` (in fact `(ρ(t_v) - 1)^{n+1} = 0`): the
substitution `X₀ ↦ X₀ - a X₂`, `X₁ ↦ X₁ - b X₂` raises the `X₂`-divisibility by one at each application and a
homogeneous polynomial of degree `n` divisible by `X₂^{n+1}` is zero.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

/-- The substitution `X₀ ↦ X₀ - a X₂`, `X₁ ↦ X₁ - b X₂`. -/
abbrev shearSub (a b : ℝ) : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  bind₁ (![X 0 - C (a : ℂ) * X 2, X 1 - C (b : ℂ) * X 2, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)

theorem X_two_dvd_shearSub_sub (a b : ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    (X 2 : MvPolynomial (Fin 3) ℂ) ∣ shearSub a b q - q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, show shearSub a b p + shearSub a b q - (p + q) =
      (shearSub a b p - p) + (shearSub a b q - q) by ring]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have hi : (X 2 : MvPolynomial (Fin 3) ℂ) ∣ shearSub a b (X i) - X i := by
      fin_cases i
      · simp [shearSub]
      · simp [shearSub]
      · simp [shearSub]
    have : shearSub a b p * shearSub a b (X i) - p * X i =
        (shearSub a b p - p) * shearSub a b (X i) + p * (shearSub a b (X i) - X i) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hi _)

/-- The shear minus the identity on polynomials. -/
def shearDelta (a b : ℝ) (q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ := shearSub a b q - q

theorem shearDelta_dvd (a b : ℝ) (j : ℕ) {q : MvPolynomial (Fin 3) ℂ}
    (hq : (X 2 : MvPolynomial (Fin 3) ℂ) ^ j ∣ q) :
    (X 2 : MvPolynomial (Fin 3) ℂ) ^ (j + 1) ∣ shearDelta a b q := by
  obtain ⟨r, rfl⟩ := hq
  have h2 : shearSub a b (X 2) = (X 2 : MvPolynomial (Fin 3) ℂ) := by simp [shearSub]
  have : shearDelta a b ((X 2 : MvPolynomial (Fin 3) ℂ) ^ j * r) =
      (X 2 : MvPolynomial (Fin 3) ℂ) ^ j * shearDelta a b r := by
    unfold shearDelta
    rw [map_mul, map_pow, h2]
    ring
  rw [this, pow_succ]
  exact mul_dvd_mul_left _ (X_two_dvd_shearSub_sub a b r)

theorem shearDelta_iter_dvd (a b : ℝ) (j : ℕ) (q : MvPolynomial (Fin 3) ℂ) :
    (X 2 : MvPolynomial (Fin 3) ℂ) ^ j ∣ (shearDelta a b)^[j] q := by
  induction j generalizing q with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact shearDelta_dvd a b j (ih q)

theorem toPoly_trL_sub_one (n : ℕ) (v : Fin 2 → ℝ) (q : Coef n) :
    Coef.toPoly ((trL n v - ContinuousLinearMap.id ℝ (Coef n)) q) =
      shearDelta (v 0) (v 1) (Coef.toPoly q) := by
  simp only [sub_apply, ContinuousLinearMap.id_apply, Coef.toPoly_sub,
    toPoly_trL, shearDelta, shearSub]
  rw [rho_transMat]

theorem toPoly_trL_sub_one_pow (n : ℕ) (v : Fin 2 → ℝ) (j : ℕ) (q : Coef n) :
    Coef.toPoly (((trL n v - ContinuousLinearMap.id ℝ (Coef n)) ^ j) q) =
      (shearDelta (v 0) (v 1))^[j] (Coef.toPoly q) := by
  induction j generalizing q with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, Function.iterate_succ_apply,
      toPoly_trL_sub_one]

theorem homogeneous_dvd_eq_zero {n : ℕ} {p : MvPolynomial (Fin 3) ℂ} (hp : p.IsHomogeneous n)
    (hd : (X 2 : MvPolynomial (Fin 3) ℂ) ^ (n + 1) ∣ p) : p = 0 := by
  obtain ⟨r, rfl⟩ := hd
  by_contra hne
  have hr : r ≠ 0 := fun h => hne (by simp [h])
  have hX : ((X 2 : MvPolynomial (Fin 3) ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (X_ne_zero 2)
  have h1 := hp.totalDegree hne
  rw [totalDegree_mul_of_isDomain hX hr, totalDegree_X_pow] at h1
  omega

theorem trL_sub_one_pow_eq_zero (n : ℕ) (v : Fin 2 → ℝ) :
    (trL n v - ContinuousLinearMap.id ℝ (Coef n)) ^ (n + 1) = 0 := by
  ext q
  apply Coef.toPoly_injective
  rw [toPoly_trL_sub_one_pow]
  have hhom : ((shearDelta (v 0) (v 1))^[n + 1] (Coef.toPoly q)).IsHomogeneous n := by
    rw [← toPoly_trL_sub_one_pow]
    exact Coef.toPoly_isHomogeneous _
  have := homogeneous_dvd_eq_zero hhom (shearDelta_iter_dvd (v 0) (v 1) (n + 1) _)
  simpa using this

theorem trL_sub_one_isNilpotent (n : ℕ) (v : Fin 2 → ℝ) :
    IsNilpotent (trL n v - ContinuousLinearMap.id ℝ (Coef n)) :=
  ⟨n + 1, trL_sub_one_pow_eq_zero n v⟩

end TernaryPeriodPolynomials.Argument.EisensteinClass
