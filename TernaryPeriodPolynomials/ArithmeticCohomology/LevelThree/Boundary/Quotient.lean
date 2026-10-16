module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Eisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.ZeroHecke

@[expose] public section


/-!
# The Hecke action on `H¹ / H¹_par` for every twist

Combining `betaInf_levelHecke` (`β_∞ ∘ T_p = q_∞ β_∞`) and `betaZero_levelHecke`
(`β_0 ∘ T_p = q_0 β_0`) with `ker β_∞ ⊓ ker β_0 = H¹_par`:

* `levelHecke_sub_mem_parabolic_of_even_sum` (`e + m` even, e.g. the good plane with `e = -1`,
  `m = n + 1`, `n` even): `T_p x - q_0 x` is parabolic;
* `levelHecke_two_step_mem_parabolic` (any twist): `(T_p - q_0)(T_p - q_∞) x` is parabolic;
* `mem_parabolicH1_of_mem_maxGenEigenspace_of_ne`: a generalized eigenvector of `T_p` whose
  eigenvalue is neither `q_∞` nor `q_0` is parabolic;
* numerics: `qInf_two_of_odd` / `qZero_two_of_odd` (`e = 0`, `p = 2`, `m` odd:
  `q_∞ = 1 - 2^{m+1} = -q_0`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryQuotient

open Matrix Module
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators ParabolicBounds TwoGenerator
open LevelThreeCosets LevelThreeHeckeH1 LevelThreeBoundaryFunctional LevelThreeBoundaryHecke
open LevelThreeBoundaryEisenstein LevelThreeBoundaryZeroHecke
open GeneralEisenstein

section Quotient

variable (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- `T_p x - q_0 x` is killed by the boundary functional at `0`. -/
theorem levelHecke_sub_mem_ker_betaZero (x : CrossedH1 (levelRep m e)) :
    levelHecke m e p hp3 x - qZero m e p • x ∈ LinearMap.ker (betaZero m e) := by
  rw [LinearMap.mem_ker, map_sub, map_smul, betaZero_levelHecke, smul_eq_mul, sub_self]

/-- For `e + m` even only the cusp `0` carries boundary classes: `T_p x - q_0 x` is parabolic. -/
theorem levelHecke_sub_mem_parabolic_of_even_sum (even : Even (e + m))
    (x : CrossedH1 (levelRep m e)) :
    levelHecke m e p hp3 x - qZero m e p • x ∈
      parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  rw [← ker_betaInf_inf_ker_betaZero, betaInf_eq_zero_of_even m e even, LinearMap.ker_zero,
    top_inf_eq]
  exact levelHecke_sub_mem_ker_betaZero m e p hp3 x

/-- If `β_∞ y = 0` then `T_p y - q_0 y` is parabolic. -/
theorem levelHecke_sub_mem_parabolic_of_betaInf_eq_zero (y : CrossedH1 (levelRep m e))
    (hy : betaInf m e y = 0) :
    levelHecke m e p hp3 y - qZero m e p • y ∈ parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  rw [← ker_betaInf_inf_ker_betaZero, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · rw [map_sub, map_smul, betaInf_levelHecke, hy]
    simp
  · rw [map_sub, map_smul, betaZero_levelHecke, smul_eq_mul, sub_self]

/-- **`(T_p - q_0)(T_p - q_∞)` maps `H¹` into the parabolic classes**, for every twist. -/
theorem levelHecke_two_step_mem_parabolic (x : CrossedH1 (levelRep m e)) :
    levelHecke m e p hp3 (levelHecke m e p hp3 x - qInf m e p • x) -
        qZero m e p • (levelHecke m e p hp3 x - qInf m e p • x) ∈
      parabolicH1 (levelRep m e) (upper 1) (lower 1) :=
  levelHecke_sub_mem_parabolic_of_betaInf_eq_zero m e p hp3 _
    (LinearMap.mem_ker.mp (levelHecke_sub_mem_ker_betaInf m e p hp3 x))

/-- **Generalized eigenvectors of `T_p` away from both Eisenstein eigenvalues are parabolic.** -/
theorem mem_parabolicH1_of_mem_maxGenEigenspace_of_ne (μ : ℂ) (hμ₁ : μ ≠ qInf m e p)
    (hμ₂ : μ ≠ qZero m e p) {x : CrossedH1 (levelRep m e)}
    (hx : x ∈ (levelHecke m e p hp3).maxGenEigenspace μ) :
    x ∈ parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  rw [mem_parabolicH1_iff]
  exact ⟨functional_eq_zero_of_mem_maxGenEigenspace (levelHecke m e p hp3) (betaInf m e)
      (qInf m e p) μ (betaInf_levelHecke m e p hp3) hμ₁ hx,
    functional_eq_zero_of_mem_maxGenEigenspace (levelHecke m e p hp3) (betaZero m e)
      (qZero m e p) μ (betaZero_levelHecke m e p hp3) hμ₂ hx⟩

end Quotient

section Numerics

/-- The trivial-twist closed form: `q_0 = p^{m+1} + ε_p^m`. -/
theorem qZero_zero_twist (m : ℕ) (p : Nat.Primes) :
    qZero m 0 p = (p.val : ℂ) ^ (m + 1) + (((signP p : ℤˣ) : ℤ) : ℂ) ^ m := by
  unfold qZero
  rw [neg_zero, zpow_zero, one_mul]

/-- **The bad line at `p = 2`** (`e = 0`, `m` odd): `q_0 = 2^{m+1} - 1`. -/
theorem qZero_two_of_odd (m : ℕ) (hm : Odd m) : qZero m 0 two = (2 : ℂ) ^ (m + 1) - 1 := by
  have h2 : (two.val : ℂ) = 2 := by simp [two]
  have hneg : ((((-1 : ℤˣ) : ℤ)) : ℂ) = -1 := by simp
  rw [qZero_zero_twist, signP_two, hneg, hm.neg_one_pow, h2]
  ring

/-- At `p = 2`, `e = 0`, `m` odd the two Eisenstein scalars are opposite: `q_∞ = -q_0`. -/
theorem qInf_two_eq_neg_qZero (m : ℕ) (hm : Odd m) : qInf m 0 two = -qZero m 0 two := by
  rw [qInf_two_of_odd m hm, qZero_two_of_odd m hm]
  ring

/-- **Lower bound for the Eisenstein scalar at `0`**: `p^{-e} (p^{m+1} - 1) ≤ ‖q_0‖`. -/
theorem norm_qZero_ge (m : ℕ) (e : ℤ) (p : Nat.Primes) :
    (p.val : ℝ) ^ (-e) * ((p.val : ℝ) ^ (m + 1) - 1) ≤ ‖qZero m e p‖ := by
  unfold qZero
  rw [norm_mul, norm_zpow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ‖(p.val : ℂ) ^ (m + 1)‖ = (p.val : ℝ) ^ (m + 1) := by
    rw [norm_pow, Complex.norm_natCast]
  have h2 : ‖(((signP p : ℤˣ) : ℤ) : ℂ) ^ m‖ = 1 := by
    rw [norm_pow, norm_signP_cast, one_pow]
  have h3 := norm_sub_le ((p.val : ℂ) ^ (m + 1) + (((signP p : ℤˣ) : ℤ) : ℂ) ^ m)
    ((((signP p : ℤˣ) : ℤ) : ℂ) ^ m)
  rw [add_sub_cancel_right, h1, h2] at h3
  linarith

theorem ne_qInf_of_norm_lt {m : ℕ} {e : ℤ} {p : Nat.Primes} (μ : ℂ)
    (h : ‖μ‖ < (p.val : ℝ) ^ (-e) * ((p.val : ℝ) ^ (m + 1) - 1)) : μ ≠ qInf m e p := by
  intro hμ
  rw [hμ] at h
  exact absurd h (not_lt.mpr (norm_qInf_ge m e p))

theorem ne_qZero_of_norm_lt {m : ℕ} {e : ℤ} {p : Nat.Primes} (μ : ℂ)
    (h : ‖μ‖ < (p.val : ℝ) ^ (-e) * ((p.val : ℝ) ^ (m + 1) - 1)) : μ ≠ qZero m e p := by
  intro hμ
  rw [hμ] at h
  exact absurd h (not_lt.mpr (norm_qZero_ge m e p))

/-- **Separation at `p = 2`, `e = 0`** (the bad line `m = n + 1 ≥ 3`): an eigenvalue of size at most
`(3/4) 2^{m+1}` is neither `q_∞` nor `q_0`. -/
theorem ne_qInf_two_of_norm_le {m : ℕ} (hm : 2 ≤ m) (μ : ℂ) (h : ‖μ‖ ≤ 3 / 4 * (2 : ℝ) ^ (m + 1)) :
    μ ≠ qInf m 0 two ∧ μ ≠ qZero m 0 two := by
  have hX : (8 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : ((two.val : ℕ) : ℝ) = 2 := by simp [two]
  have hlt : ‖μ‖ < ((two.val : ℕ) : ℝ) ^ (-(0 : ℤ)) * (((two.val : ℕ) : ℝ) ^ (m + 1) - 1) := by
    rw [h2, neg_zero, zpow_zero, one_mul]
    linarith
  exact ⟨ne_qInf_of_norm_lt μ hlt, ne_qZero_of_norm_lt μ hlt⟩

end Numerics

end TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryQuotient
