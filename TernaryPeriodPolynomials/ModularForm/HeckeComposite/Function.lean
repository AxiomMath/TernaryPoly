module

public import TernaryPeriodPolynomials.ModularForm.HeckeComposite.Arith
public import TernaryPeriodPolynomials.ModularForm.Periods.OuterLValues

@[expose] public section


/-!
# Composite Hecke operators: multiplicativity and eigenform action

* `compositeHecke_comp_coprime`: `T_m (T_n f) = T_{mn} f` for coprime `m, n` and `f` with an
  everywhere-convergent `q`-expansion.
* `compositeHecke_eigenform`: `T_m h = a_h(m) h` for every `m ≥ 1` and every normalized level-one
  eigenform `h`.

Both are proved from the `q`-series of `T_m f` (`compositeHecke_hasSum`), the coefficient formula
`compositeCoeff` (`compositeCoeff_comp_coprime`, `compositeCoeff_eq_mul`), and uniqueness of sums.
No coset decomposition of the Hecke ring is used.

Formalized by Claude Haiku 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument
open Function.Periodic
open scoped BigOperators

/-- `T_m (T_n f) = T_{mn} f` for coprime `m, n`. -/
theorem compositeHecke_comp_coprime {k : ℤ} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) (c : ℕ → ℂ) {f : UpperHalfPlane → ℂ}
    (hq : ∀ z : UpperHalfPlane, HasSum (fun N => c N * qParam 1 (z : ℂ) ^ N) (f z))
    (τ : UpperHalfPlane) :
    compositeHecke k m (compositeHecke k n f) τ = compositeHecke k (m * n) f τ := by
  have hq' : ∀ z : UpperHalfPlane,
      HasSum (fun N => compositeCoeff k n c N * qParam 1 (z : ℂ) ^ N) (compositeHecke k n f z) :=
    fun z => compositeHecke_hasSum hn c hq z
  have outer : HasSum (fun N => compositeCoeff k (m * n) c N * qParam 1 (τ : ℂ) ^ N)
      (compositeHecke k m (compositeHecke k n f) τ) := by
    have h := compositeHecke_hasSum (k := k) hm (compositeCoeff k n c) hq' τ
    simpa only [compositeCoeff_comp_coprime k c hm hn hmn] using h
  have target := compositeHecke_hasSum (k := k) (Nat.mul_pos hm hn) c hq τ
  exact outer.unique target

/-- Coefficient relation of a normalized eigenform: the prime relations for `a_h`. -/
theorem eigenform_coeff_relation {k : ℤ} (h : CuspForm levelOne k) (period : (1 : ℝ) ∈ levelOne.strictPeriods)
    (eigenvalue : Nat.Primes → ℂ) (relations : HasPrimeHeckeRelations k h eigenvalue)
    (hnorm : fourierCoeff h 1 = 1) (hc : ∀ n : ℕ, fourierCoeff h n = (UpperHalfPlane.qExpansion 1 h).coeff n)
    (p : ℕ) (hp : p.Prime) (x : ℕ) :
    fourierCoeff h p * fourierCoeff h x =
      fourierCoeff h (p * x) + (if p ∣ x then (p : ℂ) ^ (k - 1) * fourierCoeff h (x / p) else 0) := by
  have hnorm1 : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1 := (hc 1).symm.trans hnorm
  have hfirst : (UpperHalfPlane.qExpansion 1 h).coeff p = eigenvalue ⟨p, hp⟩ :=
    cuspForm_hecke_prime_coefficient h period ⟨p, hp⟩ (eigenvalue ⟨p, hp⟩) (relations ⟨p, hp⟩) hnorm1
  have key := cuspForm_hecke_coefficient h period ⟨p, hp⟩ (eigenvalue ⟨p, hp⟩) (relations ⟨p, hp⟩) x
  unfold qSeriesDilateCoefficients at key
  beta_reduce at key
  simp only [hc]
  rw [hfirst]
  by_cases hd : p ∣ x
  · rw [ite_eq_left hd] at key ⊢
    linear_combination key
  · rw [ite_eq_right hd] at key ⊢
    linear_combination key

/-- `T_m h = a_h(m) h` for every `m ≥ 1` and every normalized level-one eigenform `h`. -/
theorem compositeHecke_eigenform {k : ℤ} (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    {m : ℕ} (hm : 0 < m) (τ : UpperHalfPlane) :
    compositeHecke k m (⇑h) τ = fourierCoeff h m * h τ := by
  obtain ⟨hnorm, eigenvalue, relations⟩ := hh
  have period : (1 : ℝ) ∈ levelOne.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods
  have hc : ∀ n : ℕ, fourierCoeff h n = (UpperHalfPlane.qExpansion 1 h).coeff n := by
    intro n
    unfold fourierCoeff
    rw [Subgroup.strictWidthInfty_SL2Z]
  have hq : ∀ z : UpperHalfPlane,
      HasSum (fun n => fourierCoeff h n * qParam 1 (z : ℂ) ^ n) (h z) := by
    intro z
    have hs := ModularForm.hasSum_qExpansion h (by norm_num : (0 : ℝ) < 1) period z
    simpa only [hc] using hs
  have h0 : fourierCoeff h 0 = 0 := by
    rw [hc]
    exact CuspFormClass.qExpansion_coeff_zero h (by norm_num : (0 : ℝ) < 1) period
  have hrel : ∀ p : ℕ, p.Prime → ∀ x : ℕ,
      fourierCoeff h p * fourierCoeff h x =
        fourierCoeff h (p * x) + (if p ∣ x then (p : ℂ) ^ (k - 1) * fourierCoeff h (x / p) else 0) :=
    fun p hp x => eigenform_coeff_relation h period eigenvalue relations hnorm hc p hp x
  have hcomp := compositeCoeff_eq_mul k (fourierCoeff h) h0 hnorm hrel m
  have series : HasSum (fun N => fourierCoeff h m * (fourierCoeff h N * qParam 1 (τ : ℂ) ^ N))
      (compositeHecke k m (⇑h) τ) := by
    have hs := compositeHecke_hasSum (k := k) hm (fourierCoeff h) hq τ
    convert hs using 1
    funext N
    rw [hcomp N]
    ring
  have scaled := (hq τ).mul_left (fourierCoeff h m)
  exact series.unique scaled

end TernaryPeriodPolynomials.Argument.Identities
