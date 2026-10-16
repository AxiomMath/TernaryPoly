module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.OuterRatioProduct

@[expose] public section


/-!
# Normalisation bridge: `L^{(3)} = E_3 · L` for the global outer step

For a normalized level-one eigenform `h` of weight `k > 6` and a real `s > k/2 + 1`, the L-series
with the coefficients at multiples of `3` removed equals the full L-series times the Euler
polynomial at `3`:
`L^{(3)}(h, s) = E_3(s) · L(h, s)`, where `E_3(s) = 1 - a_3 3^{-s} + 3^{k-1-2s}`.
This is the normalisation in which the global entry of Appendix C.6 is stated.

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open Filter Topology TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The prime `3` as an element of `Nat.Primes`. -/
def threePrime : Nat.Primes := ⟨3, Nat.prime_three⟩

theorem removed_L_eq_euler_mul_full {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (s : ℝ) (hs : (k : ℝ) / 2 + 1 < s) :
    LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (s : ℂ) =
      globalOuterEulerPolynomial k (fourierCoeff h 3) ⟨3, Nat.prime_three⟩ (s : ℂ) *
        LSeries (fun m => fourierCoeff h m) (s : ℂ) := by
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
  obtain ⟨r1, r2, rsum, rprod, b1, b2⟩ :=
    cuspForm_eulerRoots h eigenvalue (fun p => (p.val : ℂ) ^ (k - 1)) initial hfirst hrec
  have E_eq (s : ℂ) (p : Nat.Primes) :
      globalOuterEulerPolynomial k (fourierCoeff h p.val) p s =
        (1 - r1 p * (p.val : ℂ) ^ (-s)) * (1 - r2 p * (p.val : ℂ) ^ (-s)) := by
    have sum_eq : r1 p + r2 p = fourierCoeff h p.val := by
      rw [rsum p]; exact (hfirst p).symm
    exact outerLValue_eulerFactor_eq p s (fourierCoeff h p.val) (r1 p) (r2 p) sum_eq (rprod p)
  have G_eq (s : ℝ) (p : Nat.Primes) :
      globalOuterFactor r1 r2 s p =
        globalOuterEulerPolynomial k (fourierCoeff h p.val) p ((s : ℝ) : ℂ) := by
    rw [E_eq]
    simp only [globalOuterFactor, scaledEulerRoot_eq_cpow]
  have summable_term := cuspForm_LSeries_norm_summable weight_positive h (s : ℂ)
    (by simpa using hs)
  -- The full product over all primes.
  obtain ⟨hP, hne, -⟩ := globalOuterFactor_package r1 r2 (k : ℝ) s (fun _ => True) b1 b2 hs
  have hall : HasProd (fun p : Nat.Primes => globalOuterFactor r1 r2 s p)
      (∏' p : {p : Nat.Primes // True}, globalOuterFactor r1 r2 s p.val) :=
    (Equiv.hasProd_iff (Equiv.subtypeUnivEquiv (fun _ : Nat.Primes => trivial))).mp hP
  have hallP : HasProd (fun p : Nat.Primes => globalOuterFactor r1 r2 s p)
      (∏' p : Nat.Primes, globalOuterFactor r1 r2 s p) := hall.multipliable.hasProd
  have hallne : ∏' p : Nat.Primes, globalOuterFactor r1 r2 s p ≠ 0 := by
    rw [hall.tprod_eq]; exact hne
  obtain ⟨hPne, hPne0, -⟩ :=
    globalOuterFactor_package r1 r2 (k : ℝ) s (fun p : Nat.Primes => p.val ≠ 3) b1 b2 hs
  -- The factor at `3` and the complement of `{3}` (`HasProd.mul_compl`, no group needed).
  let e : ↥(↑({threePrime} : Finset Nat.Primes) : Set Nat.Primes)ᶜ ≃
      {p : Nat.Primes // p.val ≠ 3} :=
    Equiv.subtypeEquivRight (fun p => by
      rw [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_singleton]
      exact not_congr ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩)
  have hb : HasProd ((fun p : Nat.Primes => globalOuterFactor r1 r2 s p) ∘
      (↑) : ↥(↑({threePrime} : Finset Nat.Primes) : Set Nat.Primes)ᶜ → ℂ)
      (∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 s p.val) :=
    (Equiv.hasProd_iff e).mpr hPne
  have ha : HasProd ((fun p : Nat.Primes => globalOuterFactor r1 r2 s p) ∘
      (↑) : ↥(↑({threePrime} : Finset Nat.Primes) : Set Nat.Primes) → ℂ)
      (∏ p ∈ ({threePrime} : Finset Nat.Primes), globalOuterFactor r1 r2 s p) :=
    Finset.hasProd _ _
  have key : ∏' p : Nat.Primes, globalOuterFactor r1 r2 s p =
      globalOuterFactor r1 r2 s threePrime *
        ∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 s p.val := by
    have hfull := HasProd.mul_compl (s := (↑({threePrime} : Finset Nat.Primes) :
      Set Nat.Primes)) ha hb
    rw [Finset.prod_singleton] at hfull
    exact hfull.tprod_eq
  have hGt : globalOuterFactor r1 r2 s threePrime ≠ 0 := by
    intro h0
    apply hallne
    rw [key, h0, zero_mul]
  have hE : globalOuterFactor r1 r2 s threePrime =
      globalOuterEulerPolynomial k (fourierCoeff h 3) ⟨3, Nat.prime_three⟩ (s : ℂ) :=
    G_eq s threePrime
  -- The full L-series is the inverse of the full product.
  have Lfull : LSeries (fun m => fourierCoeff h m) (s : ℂ) =
      (∏' p : Nat.Primes, globalOuterFactor r1 r2 s p)⁻¹ := by
    have full := quadraticEulerSeries_eq_product (fun m => fourierCoeff h m) (s : ℂ) eigenvalue
      (fun p : Nat.Primes => (p.val : ℂ) ^ (k - 1)) r1 r2 initial hmul hfirst hrec rsum rprod
      summable_term
    rw [full, ← (hasProd_inv_of_ne_zero' hallP hallne).tprod_eq]
    exact tprod_congr fun p => by simp only [globalOuterFactor, scaledEulerRoot_eq_cpow]
  -- The removed L-series is the inverse of the product over `p ≠ 3`.
  have Lrem : LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (s : ℂ) =
      (∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 s p.val)⁻¹ := by
    have prod := quadraticEulerSeries_removeFactors_eq_product
      (fun m => fourierCoeff h m) 3 (s : ℂ) eigenvalue (fun p => (p.val : ℂ) ^ (k - 1))
      r1 r2 initial hmul hfirst hrec rsum rprod summable_term
    rw [prod, ← (hasProd_inv_of_ne_zero' hPne hPne0).tprod_eq]
    let e : {p : Nat.Primes // p.val ≠ 3} ≃ {p : Nat.Primes // p.val.Coprime 3} :=
      Equiv.subtypeEquivRight
        (fun p : Nat.Primes => (Nat.coprime_primes p.property Nat.prime_three).symm)
    refine (tprod_congr fun q => ?_).trans
      (Equiv.tprod_eq e.symm (fun b : {p : Nat.Primes // p.val ≠ 3} =>
        (globalOuterFactor r1 r2 s b.val)⁻¹))
    show _ = (globalOuterFactor r1 r2 s q.val)⁻¹
    simp only [globalOuterFactor, scaledEulerRoot_eq_cpow]
  -- Conclusion: `L^{(3)} = G_3 · L` with `G_3 = E_3`.
  rw [Lrem, Lfull, key, mul_inv, ← hE, ← mul_assoc, mul_inv_cancel₀ hGt, one_mul]

/-- **Normalisation of the global entry.** For `k = n + 3 > 6`, the ratio of the removed L-series
at `n+1` and `n+2` is the ratio in the form of Appendix C.6, with the Euler factors `E_3`. -/
theorem global_entry_ratio_removed_eq (n : ℕ) (hn : 3 < n) (h : CuspForm levelOne ((n : ℤ) + 3))
    (hh : IsNormalizedEigenform h) :
    (LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 1) *
        (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 1)) +
          (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 1)))) /
      (LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 2) *
        (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 2)) +
          (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 2)))) =
      LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((n : ℂ) + 1) /
        LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((n : ℂ) + 2) := by
  have hn' : (3 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h6 : (6 : ℤ) < (n : ℤ) + 3 := by omega
  have hs1 : (((n : ℤ) + 3 : ℤ) : ℝ) / 2 + 1 < (n : ℝ) + 1 := by push_cast; linarith
  have hs2 : (((n : ℤ) + 3 : ℤ) : ℝ) / 2 + 1 < (n : ℝ) + 2 := by push_cast; linarith
  have L1 := removed_L_eq_euler_mul_full h6 h hh ((n : ℝ) + 1) hs1
  have L2 := removed_L_eq_euler_mul_full h6 h hh ((n : ℝ) + 2) hs2
  have c1 : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  have c2 : (((n : ℝ) + 2 : ℝ) : ℂ) = (n : ℂ) + 2 := by push_cast; ring
  rw [c1] at L1
  rw [c2] at L2
  have E1 : globalOuterEulerPolynomial ((n : ℤ) + 3) (fourierCoeff h 3) ⟨3, Nat.prime_three⟩
      ((n : ℂ) + 1) = 1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 1)) +
        (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 1)) := by
    have ex : (((n : ℤ) + 3 : ℤ) : ℂ) - 1 - 2 * ((n : ℂ) + 1) =
        (n : ℂ) + 2 - 2 * ((n : ℂ) + 1) := by push_cast; ring
    simp only [globalOuterEulerPolynomial, Nat.cast_ofNat, ex]
  have E2 : globalOuterEulerPolynomial ((n : ℤ) + 3) (fourierCoeff h 3) ⟨3, Nat.prime_three⟩
      ((n : ℂ) + 2) = 1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 2)) +
        (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 2)) := by
    have ex : (((n : ℤ) + 3 : ℤ) : ℂ) - 1 - 2 * ((n : ℂ) + 2) =
        (n : ℂ) + 2 - 2 * ((n : ℂ) + 2) := by push_cast; ring
    simp only [globalOuterEulerPolynomial, Nat.cast_ofNat, ex]
  rw [E1] at L1
  rw [E2] at L2
  rw [L1, L2]
  ring

end TernaryPeriodPolynomials.Argument
