module

public import TernaryPeriodPolynomials.ModularForm.Periods.OuterLValues

@[expose] public section


/-!
# Global outer step: the Euler ratio over the primes `p ≠ 3`

For a normalized level-one eigenform `h` of weight `k > 6`, the local ratios
`c_p = L_p(h,k-2) / L_p(h,k-1)` over the primes `p ≠ 3` are absolutely summable (in the
sense `∑ ‖c_p - 1‖ < ∞`), and their product is `L^{(3)}(h,k-2) / L^{(3)}(h,k-1)`, where
`L^{(3)}` is the L-series with the coefficients at multiples of `3` removed
(`removeEulerCoefficients`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open Filter Topology TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The Euler polynomial `1 - a p^{-s} + p^{k-1-2s}` at a prime `p`. -/
def globalOuterEulerPolynomial (k : ℤ) (eigenvalue : ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  1 - eigenvalue * (p.val : ℂ) ^ (-s) + (p.val : ℂ) ^ ((k : ℂ) - 1 - 2 * s)

/-- The local ratio `c_p = L_p(h,k-2) / L_p(h,k-1)`, written with the Euler polynomials. -/
def globalOuterLocalRatio (k : ℤ) (eigenvalue : ℂ) (p : Nat.Primes) : ℂ :=
  globalOuterEulerPolynomial k eigenvalue p ((k : ℂ) - 1) /
    globalOuterEulerPolynomial k eigenvalue p ((k : ℂ) - 2)

/-- The scaled quadratic Euler factor `(1 - r1 p^{-s})(1 - r2 p^{-s})`. -/
def globalOuterFactor (r1 r2 : Nat.Primes → ℂ) (s : ℝ) (p : Nat.Primes) : ℂ :=
  (1 - scaledEulerRoot r1 s p) * (1 - scaledEulerRoot r2 s p)

theorem hasProd_inv_of_ne_zero' {index : Type} {factors : index → ℂ} {limit : ℂ}
    (product : HasProd factors limit) (nonzero : limit ≠ 0) :
    HasProd (fun place => (factors place)⁻¹) limit⁻¹ := by
  unfold HasProd at product ⊢
  simp_rw [Finset.prod_inv_distrib]
  exact product.inv₀ nonzero

/-- For a subset of primes, the scaled Euler factors multiply to a nonzero absolutely
convergent product, with `∑ ‖factor - 1‖ < ∞`. -/
theorem globalOuterFactor_package (r1 r2 : Nat.Primes → ℂ) (weight s : ℝ)
    (included : Nat.Primes → Prop)
    (b1 : ∀ p, ‖r1 p‖ ≤ (p.val : ℝ) ^ (weight / 2))
    (b2 : ∀ p, ‖r2 p‖ ≤ (p.val : ℝ) ^ (weight / 2))
    (hs : weight / 2 + 1 < s) :
    HasProd (fun p : {p : Nat.Primes // included p} => globalOuterFactor r1 r2 s p.val)
        (∏' p : {p : Nat.Primes // included p}, globalOuterFactor r1 r2 s p.val) ∧
      (∏' p : {p : Nat.Primes // included p}, globalOuterFactor r1 r2 s p.val) ≠ 0 ∧
      Summable (fun p : {p : Nat.Primes // included p} =>
        ‖globalOuterFactor r1 r2 s p.val - 1‖) := by
  obtain ⟨small1, sum1⟩ := scaledEulerRoot_small_and_summable r1 weight s b1 hs
  obtain ⟨small2, sum2⟩ := scaledEulerRoot_small_and_summable r2 weight s b2 hs
  have diff := quadraticEulerFactors_summable_difference
    (fun p : {p : Nat.Primes // included p} => scaledEulerRoot r1 s p.val)
    (fun p : {p : Nat.Primes // included p} => scaledEulerRoot r2 s p.val)
    (fun p => small1 p.val) (sum1.subtype included) (sum2.subtype included)
  have nonzero : ∀ p : {p : Nat.Primes // included p},
      globalOuterFactor r1 r2 s p.val ≠ 0 := fun p =>
    quadraticEulerFactor_ne_zero (small1 p.val) (small2 p.val)
  have identity (p : {p : Nat.Primes // included p}) :
      1 + (globalOuterFactor r1 r2 s p.val - 1) = globalOuterFactor r1 r2 s p.val := by ring
  have multipliable : Multipliable (fun p : {p : Nat.Primes // included p} =>
      globalOuterFactor r1 r2 s p.val) := by
    have base := multipliable_one_add_of_summable
      (f := fun p : {p : Nat.Primes // included p} => globalOuterFactor r1 r2 s p.val - 1)
      (by simpa only [globalOuterFactor] using diff)
    simpa only [identity] using base
  refine ⟨multipliable.hasProd, ?_, ?_⟩
  · exact eulerProduct_ne_zero_of_summable_difference
      (fun p : {p : Nat.Primes // included p} => globalOuterFactor r1 r2 s p.val) nonzero
      (by simpa only [globalOuterFactor] using diff)
  · simpa only [globalOuterFactor] using diff

/-- **Global outer step (Lemma 2.5 consequence).** For a normalized level-one eigenform `h` of
weight `k > 6`, the local ratios `c_p = L_p(h,k-2)/L_p(h,k-1)` over the primes `p ≠ 3` satisfy
`∑ ‖c_p - 1‖ < ∞`, and their product is `L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`. -/
theorem outer_ratio_product {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) :
    Summable (fun p : {p : Nat.Primes // p.val ≠ 3} =>
      ‖globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val - 1‖) ∧
    HasProd (fun p : {p : Nat.Primes // p.val ≠ 3} =>
        globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val)
      (LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 1)) := by
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
  have hk' : (6 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs1 : (k : ℝ) / 2 + 1 < (k : ℝ) - 1 := by linarith
  have hs0 : (k : ℝ) / 2 + 1 < (k : ℝ) - 2 := by linarith
  obtain ⟨hP1, hP1ne, sum1⟩ := globalOuterFactor_package r1 r2 (k : ℝ) ((k : ℝ) - 1)
    (fun p : Nat.Primes => p.val ≠ 3) b1 b2 hs1
  obtain ⟨hP0, hP0ne, sum0⟩ := globalOuterFactor_package r1 r2 (k : ℝ) ((k : ℝ) - 2)
    (fun p : Nat.Primes => p.val ≠ 3) b1 b2 hs0
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
  have cast1 : (((k : ℝ) - 1 : ℝ) : ℂ) = (k : ℂ) - 1 := by simp
  have cast0 : (((k : ℝ) - 2 : ℝ) : ℂ) = (k : ℂ) - 2 := by simp
  have ratio_eq (p : Nat.Primes) :
      globalOuterLocalRatio k (fourierCoeff h p.val) p =
        globalOuterFactor r1 r2 ((k : ℝ) - 1) p / globalOuterFactor r1 r2 ((k : ℝ) - 2) p := by
    unfold globalOuterLocalRatio
    rw [G_eq, G_eq, cast1, cast0]
  have ratio_hasProd : HasProd (fun p : {p : Nat.Primes // p.val ≠ 3} =>
      globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val)
      ((∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 ((k : ℝ) - 1) p.val) *
        (∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val)⁻¹) := by
    have key : (fun p : {p : Nat.Primes // p.val ≠ 3} =>
        globalOuterLocalRatio k (fourierCoeff h p.val.val) p.val) =
        (fun p : {p : Nat.Primes // p.val ≠ 3} =>
          globalOuterFactor r1 r2 ((k : ℝ) - 1) p.val *
            (globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val)⁻¹) := by
      funext p
      rw [ratio_eq, div_eq_mul_inv]
    rw [key]
    exact hP1.mul (hasProd_inv_of_ne_zero' hP0 hP0ne)
  have L3_eq (s : ℝ) (hs : (k : ℝ) / 2 + 1 < s)
      (hP : HasProd (fun p : {p : Nat.Primes // p.val ≠ 3} =>
        globalOuterFactor r1 r2 s p.val) (∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 s p.val))
      (hne : (∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 s p.val) ≠ 0) :
      LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (s : ℂ) =
        (∏' p : {p : Nat.Primes // p.val ≠ 3}, globalOuterFactor r1 r2 s p.val)⁻¹ := by
    have summable_term := cuspForm_LSeries_norm_summable weight_positive h (s : ℂ)
      (by simpa using hs)
    have prod := quadraticEulerSeries_removeFactors_eq_product
      (fun m => fourierCoeff h m) 3 (s : ℂ) eigenvalue (fun p => (p.val : ℂ) ^ (k - 1))
      r1 r2 initial hmul hfirst hrec rsum rprod summable_term
    rw [prod, ← (hasProd_inv_of_ne_zero' hP hne).tprod_eq]
    let e : {p : Nat.Primes // p.val ≠ 3} ≃ {p : Nat.Primes // p.val.Coprime 3} :=
      Equiv.subtypeEquivRight
        (fun p : Nat.Primes => (Nat.coprime_primes p.property Nat.prime_three).symm)
    refine (tprod_congr fun q => ?_).trans
      (Equiv.tprod_eq e.symm (fun b : {p : Nat.Primes // p.val ≠ 3} =>
        (globalOuterFactor r1 r2 s b.val)⁻¹))
    show _ = (globalOuterFactor r1 r2 s q.val)⁻¹
    simp only [globalOuterFactor, scaledEulerRoot_eq_cpow]
  have L3_0 := L3_eq ((k : ℝ) - 2) hs0 hP0 hP0ne
  have L3_1 := L3_eq ((k : ℝ) - 1) hs1 hP1 hP1ne
  refine ⟨?_, ?_⟩
  · have hev : ∀ᶠ p : {p : Nat.Primes // p.val ≠ 3} in cofinite,
        ‖globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val - 1‖ < 1 / 2 :=
      sum0.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num))
    refine Summable.of_norm_bounded_eventually ((sum1.add sum0).mul_left 2) ?_
    filter_upwards [hev] with p hp
    have hnorm : 1 / 2 ≤ ‖globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val‖ := by
      have h1 := norm_sub_le (globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val)
        (globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val - 1)
      rw [sub_sub_cancel, norm_one] at h1
      linarith
    have hG0ne : globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnorm
      norm_num at hnorm
    have hnum : ‖globalOuterFactor r1 r2 ((k : ℝ) - 1) p.val -
        globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val‖ ≤
        ‖globalOuterFactor r1 r2 ((k : ℝ) - 1) p.val - 1‖ +
          ‖globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val - 1‖ := by
      have := norm_sub_le (globalOuterFactor r1 r2 ((k : ℝ) - 1) p.val - 1)
        (globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val - 1)
      rwa [sub_sub_sub_cancel_right] at this
    rw [norm_norm, ratio_eq, div_sub_one hG0ne, norm_div]
    have hX : 0 ≤ ‖globalOuterFactor r1 r2 ((k : ℝ) - 1) p.val -
        globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val‖ := norm_nonneg _
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val‖)]
    nlinarith [norm_nonneg (globalOuterFactor r1 r2 ((k : ℝ) - 1) p.val - 1),
      norm_nonneg (globalOuterFactor r1 r2 ((k : ℝ) - 2) p.val - 1)]
  · rw [← cast0, ← cast1, L3_0, L3_1, inv_div_inv]
    rw [← div_eq_mul_inv] at ratio_hasProd
    exact ratio_hasProd

end TernaryPeriodPolynomials.Argument
