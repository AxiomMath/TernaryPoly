module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ExactLevel

@[expose] public section


/-!
# The Eisenstein scalar of the level-three Hecke operators

Consequences of `LevelThreeBoundaryHecke.betaInf_levelHecke` for the level-three Levi
`Γ₁'(3)` and the coefficients `Sym^m ⊗ det^e`, with `T_p = levelHecke m e p hp3` and
`q_∞ = qInf m e p = p ^ (-e) · (ε_p ^ m · p ^ (m + 1) + 1)`:

* **`levelHecke_sub_mem_parabolic`** (`e` even): `T_p x - q_∞ • x` is a parabolic class for every
  `x`, i.e. `T_p` acts on `H¹ / H¹_par` by the scalar `q_∞` (the quotient is `0` unless `e + m` is
  odd, in which case it is `1`-dimensional, `betaInf_ne_zero`);
* `parabolicH1_eq_top`: for `e` and `e + m` even every class is parabolic;
* `mem_parabolicH1_of_mem_maxGenEigenspace` (`e` even): a generalized eigenvector of `T_p` whose
  eigenvalue is not `q_∞` is parabolic;
* `norm_qInf_ge`: `p^{-e} (p^{m+1} - 1) ≤ ‖q_∞‖`;
* the bad-line numerics at `p = 2`: `qInf_two_of_odd`, `norm_qInf_two_of_odd`
  (`m` odd, `e = 0`: `q_∞ = 1 - 2^{m+1}`, `‖q_∞‖ = 2^{m+1} - 1`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryEisenstein

open Matrix MvPolynomial Module
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators ParabolicBounds TwoGenerator
open LevelThreeCosets LevelThreeHeckeH1 LevelThreeBoundaryFunctional LevelThreeBoundaryHecke
open GeneralEisenstein

section Scalar

variable (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- `T_p x - q_∞ x` is killed by the boundary functional at `∞`. -/
theorem levelHecke_sub_mem_ker_betaInf (x : CrossedH1 (levelRep m e)) :
    levelHecke m e p hp3 x - qInf m e p • x ∈ LinearMap.ker (betaInf m e) := by
  rw [LinearMap.mem_ker, map_sub, map_smul, betaInf_levelHecke, smul_eq_mul, sub_self]

/-- **`T_p` acts on `H¹ / H¹_par` by the Eisenstein scalar `q_∞`** (`e` even, so that the cusp
at `0` carries no boundary class). -/
theorem levelHecke_sub_mem_parabolic (even : Even e) (x : CrossedH1 (levelRep m e)) :
    levelHecke m e p hp3 x - qInf m e p • x ∈
      parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  rw [parabolicH1_eq_ker_betaInf m e even]
  exact levelHecke_sub_mem_ker_betaInf m e p hp3 x

/-- If both `e` and `e + m` are even, every class is parabolic. -/
theorem mem_parabolicH1_of_even_even (evenE : Even e) (evenSum : Even (e + m))
    (x : CrossedH1 (levelRep m e)) :
    x ∈ parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  rw [parabolicH1_eq_top m e evenE evenSum]
  exact Submodule.mem_top

/-- An eigenfunctional kills generalized eigenvectors of any other eigenvalue. -/
theorem functional_eq_zero_of_mem_maxGenEigenspace {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (β : V →ₗ[ℂ] ℂ) (q μ : ℂ) (hβ : ∀ x, β (A x) = q * β x) (hμ : μ ≠ q)
    {x : V} (hx : x ∈ A.maxGenEigenspace μ) : β x = 0 := by
  rw [Module.End.mem_maxGenEigenspace] at hx
  obtain ⟨k, hk⟩ := hx
  have hpow : ∀ (n : ℕ) (y : V), β (((A - μ • 1) ^ n) y) = (q - μ) ^ n * β y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smul, hβ, smul_eq_mul]
      ring
  have h := hpow k x
  rw [hk, map_zero] at h
  have hq : (q - μ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hμ))
  exact (mul_eq_zero.mp h.symm).resolve_left hq

/-- **Generalized eigenvectors away from the Eisenstein eigenvalue are parabolic** (`e` even). -/
theorem mem_parabolicH1_of_mem_maxGenEigenspace (even : Even e) (μ : ℂ) (hμ : μ ≠ qInf m e p)
    {x : CrossedH1 (levelRep m e)} (hx : x ∈ (levelHecke m e p hp3).maxGenEigenspace μ) :
    x ∈ parabolicH1 (levelRep m e) (upper 1) (lower 1) := by
  rw [parabolicH1_eq_ker_betaInf m e even, LinearMap.mem_ker]
  exact functional_eq_zero_of_mem_maxGenEigenspace (levelHecke m e p hp3) (betaInf m e)
    (qInf m e p) μ (betaInf_levelHecke m e p hp3) hμ hx

end Scalar

section Nonvanishing

variable (m : ℕ) (e : ℤ)

/-- **The Eisenstein class exists**: for `m > 0`, `e` even and `e + m` odd, `β_∞ ≠ 0`, so
`H¹ / H¹_par` is one-dimensional. -/
theorem betaInf_ne_zero (positive : 0 < m) (even : Even e) (odd : ¬ Even (e + m)) :
    betaInf m e ≠ 0 := by
  intro h0
  have hpar : parabolicH1 (levelRep m e) (upper 1) (lower 1) = ⊤ := by
    rw [parabolicH1_eq_ker_betaInf m e even, h0, LinearMap.ker_zero]
  have h1 := ExactLevel.finrank_level_H1_eq (m := m) e positive
  have h2 := ExactLevel.finrank_level_parabolicH1_eq (m := m) e positive
  rw [hpar, finrank_top] at h2
  rw [ite_eq_right odd, ite_eq_left even] at h1
  omega

/-- For `m > 0`, `e` even, `e + m` odd: `dim H¹ = dim H¹_par + 1`. -/
theorem finrank_H1_eq_parabolic_add_one (positive : 0 < m) (even : Even e)
    (odd : ¬ Even (e + m)) :
    finrank ℂ (CrossedH1 (levelRep m e)) =
      finrank ℂ (parabolicH1 (levelRep m e) (upper 1) (lower 1)) + 1 := by
  have h1 := ExactLevel.finrank_level_H1_eq (m := m) e positive
  have h2 := ExactLevel.finrank_level_parabolicH1_eq (m := m) e positive
  rw [ite_eq_right odd, ite_eq_left even] at h1
  omega

end Nonvanishing

/-- `0` is an even integer. -/
theorem even_zero_int : Even (0 : ℤ) := ⟨0, rfl⟩

section BadLine

/-- **The bad line**: on the Levi cohomology `H¹(Γ₁'(3), Sym^{n+1})` of Sol's bad-line interface,
`T_p x - q_∞ x` is parabolic, `q_∞ = ε_p^{n+1} p^{n+2} + 1`. -/
theorem badLevelHecke_sub_mem_parabolic (n : ℕ) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (x : CrossedH1 (binaryArithmeticRepresentation n)) :
    badLevelHecke p hp3 n x - qInf (n + 1) 0 p • x ∈
      parabolicH1 (levelRep (n + 1) 0) (upper 1) (lower 1) :=
  levelHecke_sub_mem_parabolic (n + 1) 0 p hp3 even_zero_int x

/-- For `n` odd every bad-line Levi class is parabolic (no Eisenstein quotient). -/
theorem badLevel_parabolicH1_eq_top (n : ℕ) (h : Even (n + 1)) :
    parabolicH1 (levelRep (n + 1) 0) (upper 1) (lower 1) = ⊤ :=
  parabolicH1_eq_top (n + 1) 0 even_zero_int (by rw [zero_add, Int.even_coe_nat]; exact h)

/-- For `n` even the bad-line quotient `H¹ / H¹_par` is one-dimensional: `β_∞ ≠ 0`. -/
theorem badLevel_betaInf_ne_zero (n : ℕ) (h : ¬ Even (n + 1)) : betaInf (n + 1) 0 ≠ 0 :=
  betaInf_ne_zero (n + 1) 0 (Nat.succ_pos n) even_zero_int
    (by rw [zero_add, Int.even_coe_nat]; exact h)

end BadLine

section Numerics

/-- The prime `2`. -/
def two : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- `ε_2 = -1` (as `2 ≡ -1 mod 3`). -/
theorem signP_two : signP two = -1 := by
  have h : ((two.val : ℕ) : ZMod 3) ≠ 1 := by decide
  unfold signP
  rw [ite_eq_right h]

theorem norm_signP_cast (p : Nat.Primes) : ‖(((signP p : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (signP p) with h | h <;> simp [h]

/-- The closed form of the scalar for the trivial twist (the bad-line coefficients,
`m = degree + 1`): `q_∞ = ε_p ^ m p ^ (m + 1) + 1`. -/
theorem qInf_zero_twist (m : ℕ) (p : Nat.Primes) :
    qInf m 0 p = (((signP p : ℤˣ) : ℤ) : ℂ) ^ m * (p.val : ℂ) ^ (m + 1) + 1 := by
  unfold qInf
  rw [neg_zero, zpow_zero, one_mul]

/-- **Lower bound for the Eisenstein scalar**: `p^{-e} (p^{m+1} - 1) ≤ ‖q_∞‖`. -/
theorem norm_qInf_ge (m : ℕ) (e : ℤ) (p : Nat.Primes) :
    (p.val : ℝ) ^ (-e) * ((p.val : ℝ) ^ (m + 1) - 1) ≤ ‖qInf m e p‖ := by
  unfold qInf
  rw [norm_mul, norm_zpow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ‖(((signP p : ℤˣ) : ℤ) : ℂ) ^ m * (p.val : ℂ) ^ (m + 1)‖ = (p.val : ℝ) ^ (m + 1) := by
    rw [norm_mul, norm_pow, norm_pow, norm_signP_cast, one_pow, one_mul, Complex.norm_natCast]
  have h2 : ‖(((signP p : ℤˣ) : ℤ) : ℂ) ^ m * (p.val : ℂ) ^ (m + 1)‖ ≤
      ‖(((signP p : ℤˣ) : ℤ) : ℂ) ^ m * (p.val : ℂ) ^ (m + 1) + 1‖ + 1 := by
    have h := norm_sub_le ((((signP p : ℤˣ) : ℤ) : ℂ) ^ m * (p.val : ℂ) ^ (m + 1) + 1) 1
    rwa [add_sub_cancel_right, norm_one] at h
  linarith

/-- **The bad line at `p = 2`** (`e = 0`, `m` odd, e.g. `m = n + 1`, `n` even):
`q_∞ = 1 - 2^{m+1}`. -/
theorem qInf_two_of_odd (m : ℕ) (hm : Odd m) : qInf m 0 two = 1 - (2 : ℂ) ^ (m + 1) := by
  have h2 : (two.val : ℂ) = 2 := by simp [two]
  have hneg : ((((-1 : ℤˣ) : ℤ)) : ℂ) = -1 := by simp
  rw [qInf_zero_twist, signP_two, hneg, hm.neg_one_pow, h2]
  ring

/-- `‖q_∞‖ = 2^{m+1} - 1` at `p = 2`, `e = 0`, `m` odd. -/
theorem norm_qInf_two_of_odd (m : ℕ) (hm : Odd m) : ‖qInf m 0 two‖ = (2 : ℝ) ^ (m + 1) - 1 := by
  have hone : (1 : ℝ) ≤ 2 ^ (m + 1) := by
    have h0 : (0 : ℕ) < 2 ^ (m + 1) := by positivity
    have h : (1 : ℕ) ≤ 2 ^ (m + 1) := h0
    exact_mod_cast h
  rw [qInf_two_of_odd m hm, norm_sub_rev]
  have hcast : (2 : ℂ) ^ (m + 1) - 1 = (((2 : ℝ) ^ (m + 1) - 1 : ℝ) : ℂ) := by
    simp
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (m + 1) - 1 := by linarith
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg hnn]

end Numerics

end TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryEisenstein
