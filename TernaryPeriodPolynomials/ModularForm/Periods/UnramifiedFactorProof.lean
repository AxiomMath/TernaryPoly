module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.QExpansion
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.Series
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.EulerValues
public import TernaryPeriodPolynomials.ModularForm.Periods.OuterLValues

@[expose] public section



/-!
# Appendix C.6 unramified local factor

Proof of `unramified_local_factor` (target (d)): for a normalized level-one eigenform `h` of
weight `k > 6` and a prime `p`, the shell sum over valuations `r ≥ 1` converges and, together
with the contribution `1` of `ℤ_p²`, sums to the ratio of local Euler factors
`L_p(h,k-2)/L_p(h,k-1)`.

The key identity: writing `x := p^{2-k}` and `F(x) := ∑' e, a_h(p^e) x^e`, the shell sum equals
`F(x)(1-x) - 1` (using the Hecke generating function and the algebraic fact `p^{k-2} x^2 = x`),
and `1 + (1-p⁻¹)(F(x)(1-x)-1)` simplifies to the stated ratio using `D·F(x) = 1` where
`D = 1 - a_h(p) x + p^{k-1} x^2` is exactly the local factor at `s = k-2`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem unramified_local_factor' {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (p : Nat.Primes) :
    Summable (fun r : ℕ => ((p : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
      (fourierCoeff h ((p : ℕ) ^ (r + 1)) -
        ((p : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h ((p : ℕ) ^ (r - 1))))) ∧
    1 + (1 - ((p : ℕ) : ℂ)⁻¹) * ∑' r : ℕ, ((p : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
      (fourierCoeff h ((p : ℕ) ^ (r + 1)) -
        ((p : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h ((p : ℕ) ^ (r - 1)))) =
    (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) + ((p : ℕ) : ℂ) ^ (1 - k)) /
      (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k)) := by
  obtain ⟨initial, eigenvalue, relations⟩ := hh
  have pnonzero : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.pos.ne'
  have pnn : (0:ℝ) ≤ (p.val:ℝ) := by exact_mod_cast p.property.pos.le
  have pR : (1:ℝ) < (p.val:ℝ) := by exact_mod_cast p.property.one_lt
  -- preamble: bridge the width-1 Hecke facts to `levelOne.strictWidthInfty`-phrasing
  have period : (1 : ℝ) ∈ levelOne.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods
  have initial' : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1 := by
    have widened : (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff 1 = 1 := initial
    rwa [Subgroup.strictWidthInfty_SL2Z] at widened
  have hfirst : (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff p.val =
      eigenvalue p := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_coefficient h period p (eigenvalue p) (relations p) initial'
  have hrec : ∀ e : ℕ,
      (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ (e + 2)) =
        eigenvalue p * (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff
            (p.val ^ (e + 1)) -
          (p.val : ℂ) ^ (k - 1) *
            (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ e) := by
    intro e
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_power_recurrence h period p (eigenvalue p) (relations p) e
  have hfc : fourierCoeff h p.val = eigenvalue p := hfirst
  -- the coefficient sequence along powers of `p`, as a plain function
  let coeffs : ℕ → ℂ :=
    fun e => (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ e)
  have coeffs0 : coeffs 0 = 1 := by
    show (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ 0) = 1
    rw [pow_zero]; exact initial
  have coeffs1 : coeffs 1 = eigenvalue p := by
    show (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ 1) = eigenvalue p
    rw [pow_one]; exact hfirst
  have coeffsrec : ∀ e : ℕ, coeffs (e + 2) = eigenvalue p * coeffs (e + 1) -
      (p.val : ℂ) ^ (k - 1) * coeffs e := hrec
  -- the scale `x = p^{2-k}`
  set x : ℂ := (p.val : ℂ) ^ ((2 : ℤ) - k) with hx_def
  have hxnorm : ‖x‖ = (p.val:ℝ) ^ ((2:ℤ) - k) := by
    rw [hx_def, Complex.norm_zpow]; norm_num
  -- exponent identities relating integer powers of `p` to `x`
  have hx2 : (p.val:ℂ) ^ (k - 2) = x⁻¹ := by
    rw [hx_def, ← zpow_neg]; congr 1; ring
  have hx1minus : (p.val:ℂ) ^ (1 - k) = x * (p.val:ℂ)⁻¹ := by
    rw [hx_def, ← zpow_neg_one (p.val:ℂ), ← zpow_add₀ pnonzero]; congr 1; ring
  have hx2minus : (p.val : ℂ) ^ ((2:ℤ) - k) = x := hx_def
  have hx3' : (p.val:ℂ) ^ (k - 1) * x ^ 2 = (p.val:ℂ) ^ (3 - k) := by
    rw [hx_def, ← zpow_natCast ((p.val:ℂ) ^ ((2:ℤ) - k)) 2, ← zpow_mul, ← zpow_add₀ pnonzero]
    congr 1; push_cast; ring
  -- the key algebraic identity `p^{k-2} x^2 = x`
  have hkey : (p.val:ℂ) ^ (k - 2) * x ^ 2 = x := by
    rw [hx2]; field_simp
  -- the zpow-to-npow identity converting the target's shell weight to `x^(r+1)`
  have hzpow : ∀ r : ℕ,
      ((p.val:ℂ)) ^ (-(((r : ℤ) + 1) * (k - 2))) = x ^ (r + 1) := by
    intro r
    have exponent_eq : (-(((r : ℤ) + 1) * (k - 2))) = ((2:ℤ) - k) * ((r + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [exponent_eq, zpow_mul, hx2minus, zpow_natCast]
  -- summability of `coeffs e * x^e` via the Ramanujan-type coefficient bound
  obtain ⟨C, Cpos, hbound⟩ := cuspForm_primePowerCoefficient_bound h
  have hsummable : Summable (fun e : ℕ => coeffs e * x ^ e) := by
    set ρ : ℝ := (p.val:ℝ) ^ (2 - (k:ℝ)/2) with hρ_def
    have hρlt : ρ < 1 := by
      rw [hρ_def]
      apply Real.rpow_lt_one_of_one_lt_of_neg pR
      have hk6 : (6:ℝ) < (k:ℝ) := by exact_mod_cast hk
      linarith
    have hρnn : 0 ≤ ρ := by rw [hρ_def]; positivity
    apply Summable.of_norm_bounded
      (Summable.mul_left C (summable_geometric_of_lt_one hρnn hρlt))
    intro e
    have hb := hbound p e
    have step1 : ‖coeffs e * x ^ e‖ ≤ C * (((p.val:ℝ) ^ e) ^ ((k:ℝ)/2)) * ‖x‖ ^ e := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    refine step1.trans_eq ?_
    have commute : ((p.val:ℝ) ^ e) ^ ((k:ℝ)/2) = ((p.val:ℝ) ^ ((k:ℝ)/2)) ^ e := by
      rw [← Real.rpow_natCast (p.val:ℝ) e, ← Real.rpow_mul pnn,
        mul_comm (e:ℝ) ((k:ℝ)/2), Real.rpow_mul pnn, Real.rpow_natCast]
    have hbase : (p.val:ℝ) ^ ((k:ℝ)/2) * ‖x‖ = ρ := by
      rw [hxnorm, ← Real.rpow_intCast (p.val:ℝ) ((2:ℤ) - k),
        ← Real.rpow_add (by linarith : (0:ℝ) < (p.val:ℝ)), hρ_def]
      congr 1; push_cast; ring
    rw [commute, mul_assoc, ← mul_pow, hbase]
  -- the generating-function identity `D * F(x) = 1`
  have hDinv : (∑' e, coeffs e * x ^ e) =
      (1 - eigenvalue p * x + (p.val:ℂ) ^ (k - 1) * x ^ 2)⁻¹ :=
    quadraticRecurrence_weighted_tsum_eq_inverse coeffs (eigenvalue p) ((p.val:ℂ) ^ (k - 1)) x
      coeffs0 coeffs1 coeffsrec hsummable
  -- `D ≠ 0` via the already-proved Lemma 2.5 (target (a)), specialised to `S = {p}`, `s = k - 2`
  have hDne : (1 - eigenvalue p * x + (p.val:ℂ) ^ (k - 1) * x ^ 2) ≠ 0 := by
    have hA := lemma_2_5' hk h ⟨initial, eigenvalue, relations⟩ {p} ((k:ℂ) - 2) (Or.inl rfl)
    rw [Finset.prod_singleton] at hA
    have hfactor := (mul_ne_zero_iff.mp hA).2
    have econv : ((p.val:ℂ)) ^ (-((k:ℂ) - 2)) = x := by
      rw [show (-((k:ℂ) - 2)) = (((2:ℤ) - k : ℤ) : ℂ) by push_cast; ring,
        Complex.cpow_intCast, hx2minus]
    have econv2 : ((p.val:ℂ)) ^ ((k:ℂ) - 1 - 2 * ((k:ℂ) - 2)) = (p.val:ℂ) ^ (k - 1) * x ^ 2 := by
      have exponent_eq : ((k:ℂ) - 1 - 2 * ((k:ℂ) - 2)) =
          (((k - 1 : ℤ)) : ℂ) + (((2:ℤ) - k : ℤ) : ℂ) * ((2:ℕ):ℂ) := by push_cast; ring
      rw [exponent_eq, Complex.cpow_add _ _ pnonzero, Complex.cpow_intCast,
        Complex.cpow_mul_nat, Complex.cpow_intCast, hx2minus]
    rw [econv, econv2, hfc] at hfactor
    exact hfactor
  have hF : (1 - eigenvalue p * x + (p.val:ℂ) ^ (k - 1) * x ^ 2) * (∑' e, coeffs e * x ^ e) = 1 := by
    rw [hDinv]; exact mul_inv_cancel₀ hDne
  -- splitting the shell sum
  let shiftedCoeffs : ℕ → ℂ := fun r => if r = 0 then 0 else coeffs (r - 1)
  have hpiece1_summable : Summable (fun r : ℕ => coeffs (r + 1) * x ^ (r + 1)) :=
    (summable_nat_add_iff 1).mpr hsummable
  have hpiece2_summable : Summable (fun r : ℕ => x ^ (r + 1) * shiftedCoeffs r) := by
    have hf' : Summable (fun e : ℕ => x ^ 2 * (coeffs e * x ^ e)) := hsummable.mul_left (x ^ 2)
    have hshift : Summable (fun n : ℕ => x ^ (n + 1 + 1) * shiftedCoeffs (n + 1)) := by
      have heq : (fun n : ℕ => x ^ (n + 1 + 1) * shiftedCoeffs (n + 1)) =
          (fun e : ℕ => x ^ 2 * (coeffs e * x ^ e)) := by
        funext n
        show x ^ (n + 1 + 1) * (if n + 1 = 0 then (0:ℂ) else coeffs (n + 1 - 1)) =
          x ^ 2 * (coeffs n * x ^ n)
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
        ring
      rw [heq]; exact hf'
    exact (summable_nat_add_iff 1).mp hshift
  have hshell_summable :
      Summable (fun r : ℕ => x ^ (r + 1) * (coeffs (r + 1) - (p.val:ℂ) ^ (k - 2) * shiftedCoeffs r)) := by
    have hsplit' : (fun r : ℕ => x ^ (r + 1) * (coeffs (r + 1) - (p.val:ℂ) ^ (k - 2) * shiftedCoeffs r)) =
        (fun r : ℕ => coeffs (r + 1) * x ^ (r + 1) -
          (p.val:ℂ) ^ (k - 2) * (x ^ (r + 1) * shiftedCoeffs r)) := by
      funext r; ring
    rw [hsplit']
    exact hpiece1_summable.sub (hpiece2_summable.mul_left _)
  have hpiece1 : (∑' r : ℕ, coeffs (r + 1) * x ^ (r + 1)) = (∑' e, coeffs e * x ^ e) - 1 := by
    have heq0 := hsummable.tsum_eq_zero_add
    rw [coeffs0] at heq0
    simp only [pow_zero, mul_one] at heq0
    rw [heq0]; ring
  have hpiece2 : (∑' r : ℕ, x ^ (r + 1) * shiftedCoeffs r) = x ^ 2 * (∑' e, coeffs e * x ^ e) := by
    have heq0 := hpiece2_summable.tsum_eq_zero_add
    have e0 : x ^ (0 + 1) * shiftedCoeffs 0 = 0 := by
      show x ^ (0 + 1) * (if (0:ℕ) = 0 then (0:ℂ) else coeffs (0 - 1)) = 0
      simp
    have erec : ∀ n : ℕ, x ^ (n + 1 + 1) * shiftedCoeffs (n + 1) = x ^ 2 * (coeffs n * x ^ n) := by
      intro n
      show x ^ (n + 1 + 1) * (if n + 1 = 0 then (0:ℂ) else coeffs (n + 1 - 1)) =
        x ^ 2 * (coeffs n * x ^ n)
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      ring
    rw [e0, zero_add] at heq0
    rw [heq0, tsum_congr erec, tsum_mul_left]
  have hshell_eq :
      (∑' r : ℕ, x ^ (r + 1) * (coeffs (r + 1) - (p.val:ℂ) ^ (k - 2) * shiftedCoeffs r)) =
      (∑' e, coeffs e * x ^ e) * (1 - x) - 1 := by
    have hsplit : (fun r : ℕ => x ^ (r + 1) * (coeffs (r + 1) - (p.val:ℂ) ^ (k - 2) * shiftedCoeffs r)) =
        (fun r : ℕ => coeffs (r + 1) * x ^ (r + 1) -
          (p.val:ℂ) ^ (k - 2) * (x ^ (r + 1) * shiftedCoeffs r)) := by
      funext r; ring
    rw [hsplit, hpiece1_summable.tsum_sub (hpiece2_summable.mul_left _), tsum_mul_left,
      hpiece1, hpiece2, ← mul_assoc, hkey]
    ring
  -- the target's numerator/denominator, rewritten in terms of `eigenvalue p`, `x`, `p`
  have hDeq : (1 - eigenvalue p * x + (p.val:ℂ) ^ (k - 1) * x ^ 2) =
      (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k)) := by
    rw [hx3', hfc, hx2minus]
  have hNeq : (1 - eigenvalue p * (x * (p.val:ℂ)⁻¹) + (x * (p.val:ℂ)⁻¹)) =
      (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) + ((p : ℕ) : ℂ) ^ (1 - k)) := by
    rw [hfc, hx1minus]
  -- the key cross-scale identity `p^{k-1} x^2 p^{-1} = x`, i.e. `A x P⁻¹ = 1`
  have hAx : (p.val:ℂ) ^ (k - 1) * x ^ 2 * (p.val:ℂ)⁻¹ = x := by
    rw [hx3', ← zpow_neg_one (p.val:ℂ), ← zpow_add₀ pnonzero,
      show (3 - k : ℤ) + (-1) = (2:ℤ) - k from by ring]
  -- pointwise identity between the target's shell summand and the `x`-phrased one
  have heq : ∀ r : ℕ, ((p : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
      (fourierCoeff h ((p : ℕ) ^ (r + 1)) -
        ((p : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h ((p : ℕ) ^ (r - 1)))) =
      x ^ (r + 1) * (coeffs (r + 1) - (p.val:ℂ) ^ (k - 2) * shiftedCoeffs r) := by
    intro r
    rw [hzpow r]
    rfl
  refine ⟨?_, ?_⟩
  · have hfun_eq : (fun r : ℕ => ((p : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
        (fourierCoeff h ((p : ℕ) ^ (r + 1)) -
          ((p : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h ((p : ℕ) ^ (r - 1))))) =
        (fun r : ℕ => x ^ (r + 1) * (coeffs (r + 1) - (p.val:ℂ) ^ (k - 2) * shiftedCoeffs r)) :=
      funext heq
    rw [hfun_eq]
    exact hshell_summable
  · rw [tsum_congr heq, hshell_eq, ← hNeq, ← hDeq, eq_div_iff hDne]
    linear_combination (1 - (p.val:ℂ)⁻¹) * (1 - x) * hF + hAx

end TernaryPeriodPolynomials.Argument
