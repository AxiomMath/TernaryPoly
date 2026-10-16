module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.LValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.QExpansion
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OuterEulerValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.Nonvanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RemovedEulerFactors

@[expose] public section


/-!
# Lemma 2.5: nonvanishing of outer L-values

Proof of `lSeries_outer_critical_ne_zero` (target (a)): for a normalized level-one eigenform `h` of weight
`k > 6`, `L(h,s) * ∏_{p ∈ S} (1 - a_h(p) p^{-s} + p^{k-1-2s}) ≠ 0` at `s = k-2, k-1`, for any
finite set `S` of primes.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A quadratic Euler factor splits into its two root factors (algebraic identity, using
`cpow`/`zpow` bridging). -/
theorem outerLValue_eulerFactor_eq {k : ℤ} (p : Nat.Primes) (s a root1 root2 : ℂ)
    (sum_eq : root1 + root2 = a) (product_eq : root1 * root2 = (p.val : ℂ) ^ (k - 1)) :
    1 - a * (p.val : ℂ) ^ (-s) + (p.val : ℂ) ^ ((k : ℂ) - 1 - 2 * s) =
      (1 - root1 * (p.val : ℂ) ^ (-s)) * (1 - root2 * (p.val : ℂ) ^ (-s)) := by
  have nonzero : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.pos.ne'
  have exponent_eq :
      (p.val : ℂ) ^ (k - 1) * ((p.val : ℂ) ^ (-s)) ^ 2 = (p.val : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_mul_nat, ← Complex.cpow_add _ _ nonzero]
    congr 1
    push_cast
    ring
  rw [← exponent_eq, ← sum_eq, ← product_eq]
  ring

/-- Auxiliary form of Lemma 2.5, generic in the real `argument` (rather than fixed to
`k - 2` or `k - 1`). -/
theorem lemma_2_5_aux {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (S : Finset Nat.Primes) (argument : ℝ)
    (argument_bound : (k : ℝ) / 2 + 1 < argument) :
    LSeries (fun m => fourierCoeff h m) (argument : ℂ) *
      ∏ p ∈ S, (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(argument : ℂ)) +
        ((p : ℕ) : ℂ) ^ ((k : ℂ) - 1 - 2 * (argument : ℂ))) ≠ 0 := by
  obtain ⟨initial, eigenvalue, relations⟩ := hh
  have weight_positive : (0 : ℤ) < k := by omega
  have period : (1 : ℝ) ∈ levelOne.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods
  have initial' : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1 := by
    have widened : (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff 1 = 1 := initial
    rwa [Subgroup.strictWidthInfty_SL2Z] at widened
  have hmul : ∀ a b : ℕ, a.Coprime b →
      (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (a * b) =
        (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff a *
          (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff b := by
    intro a b hab
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_multiplicative h period eigenvalue relations initial' a b hab
  have hfirst : ∀ p : Nat.Primes,
      (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff p.val = eigenvalue p := by
    intro p
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_coefficient h period p (eigenvalue p) (relations p) initial'
  have hrec : ∀ (p : Nat.Primes) (e : ℕ),
      (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ (e + 2)) =
        eigenvalue p * (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff
            (p.val ^ (e + 1)) -
          (p.val : ℂ) ^ (k - 1) *
            (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ e) := by
    intro p e
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_power_recurrence h period p (eigenvalue p) (relations p) e
  obtain ⟨first_root, second_root, root_sum, root_product, first_bound, second_bound⟩ :=
    cuspForm_eulerRoots h eigenvalue (fun p => (p.val : ℂ) ^ (k - 1)) initial hfirst hrec
  have lseries_ne : LSeries (fun m => fourierCoeff h m) (argument : ℂ) ≠ 0 :=
    cuspForm_LSeries_ne_zero_of_recurrence weight_positive h argument argument_bound eigenvalue
      (fun p => (p.val : ℂ) ^ (k - 1)) initial hmul hfirst hrec
  have factor_ne : ∀ p ∈ S, (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(argument : ℂ)) +
      ((p : ℕ) : ℂ) ^ ((k : ℂ) - 1 - 2 * (argument : ℂ))) ≠ 0 := by
    intro p _
    have sum_eq : first_root p + second_root p = fourierCoeff h p.val := by
      rw [root_sum p]; exact (hfirst p).symm
    have identity := outerLValue_eulerFactor_eq p (argument : ℂ) (fourierCoeff h p.val)
      (first_root p) (second_root p) sum_eq (root_product p)
    rw [identity]
    have first_small :=
      (scaledEulerRoot_small_and_summable first_root (k : ℝ) argument first_bound
        argument_bound).1 p
    have second_small :=
      (scaledEulerRoot_small_and_summable second_root (k : ℝ) argument second_bound
        argument_bound).1 p
    rw [scaledEulerRoot_eq_cpow] at first_small second_small
    exact quadraticEulerFactor_ne_zero first_small second_small
  exact mul_ne_zero lseries_ne (Finset.prod_ne_zero_iff.mpr factor_ne)

theorem lemma_2_5' {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (S : Finset Nat.Primes) (s : ℂ) (hs : s = (k : ℂ) - 2 ∨ s = (k : ℂ) - 1) :
    LSeries (fun m => fourierCoeff h m) s *
      ∏ p ∈ S, (1 - fourierCoeff h (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)) +
        ((p : ℕ) : ℂ) ^ ((k : ℂ) - 1 - 2 * s)) ≠ 0 := by
  have hk' : (6 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  obtain hs | hs := hs <;> subst hs
  · simpa only [Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat,
      Complex.ofReal_one] using lemma_2_5_aux hk h hh S ((k : ℝ) - 2) (by linarith)
  · simpa only [Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat,
      Complex.ofReal_one] using lemma_2_5_aux hk h hh S ((k : ℝ) - 1) (by linarith)

end TernaryPeriodPolynomials.Argument
