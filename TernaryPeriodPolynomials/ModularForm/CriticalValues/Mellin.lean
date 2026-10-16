module

public import TernaryPeriodPolynomials.ModularForm.BinaryCuspOuter
public import TernaryPeriodPolynomials.ModularForm.Period.Axis
public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Swap
public import TernaryPeriodPolynomials.PeriodPolynomial.Defs

@[expose] public section


/-!
# Mellin transform and critical `L`-values: the coefficients of the period polynomial

Formalized by Claude Sonnet 5.5.
Paper: `eq:period-critical-coefficients`, the conventions of the paper, `eq:even-period-normalization`.

For `h` a level-one cusp form of weight `k = n + 2` and `Λ(h,s) := (2π)^{-s} Γ(s) L(h,s)` (`completedL`, with `L = ModularForm.L` the entire
continuation of `∑ a_h(m) m^{-s}`):

* `moment_eq_gamma_mul_L`: the imaginary-axis Mellin transform is `(2π)^{-s} Γ(s) L(h,s)` at every `s` with `Γℂ(s) ≠ 0` (this generalizes
  `TernaryPoly.BinaryCuspPeriod.moment_nat_eq`, which is the point `s = d`);
* `periodMoment_eq_completedL`, `axis_integral_eq`: `∫₀^∞ h(iy) y^j dy = Λ(h, j+1)` and `∫₀^{i∞} h(τ) τ^j dτ = i^{j+1} Γ(j+1) (2π)^{-j-1} L(h, j+1)` for
  all `j` (the critical integers are `j + 1 = 1, …, k - 1`);
* `periodPolynomial_eq_critical`: `eq:period-critical-coefficients` literally;
* `lseries_eq_L_of_re`, `completedL_eq_lseries`: for `Re s > k/2 + 1` the continuation is the Dirichlet series;
* `evenPeriodPart_eq_critical`, `oddPeriodPart_eq_critical`: the parts of `r_h` in `X`; `completedL_reflection` (`Λ(h,k-s) = i^k Λ(h,s)`), `axis_identity`
  (`i Λ(h,1) = - i^{n+1} Λ(h,n+1)`), `eval_evenPeriodPart_one_zero` (`r_h^{ev}(1,0) = i Λ(h,1)`): the axis normalization in terms of `L`-values.
-/

open Complex MeasureTheory MvPolynomial
open UpperHalfPlane hiding I
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CriticalValues

open TernaryPoly.BinaryCuspPeriod TernaryPeriodPolynomials.Argument

/-- **The Mellin transform of the imaginary-axis restriction at every argument with a nonvanishing complex Gamma factor**:
`∫₀^∞ f(it) t^{s-1} dt = (2π)^{-s} Γ(s) L(f, s)`, where `L` is the entire continuation of the Dirichlet series
(`ModularForm.L`). This generalizes `TernaryPoly.BinaryCuspPeriod.moment_nat_eq` (the point `s = d`) to all `s`. -/
theorem moment_eq_gamma_mul_L {d : ℕ} (f : Forms d) (s : ℂ) (hs : Gammaℂ s ≠ 0) :
    moment f s = Gamma s / (2 * (Real.pi : ℂ)) ^ s * ModularForm.L (weight_pos d) f s := by
  have hp : (2 * (Real.pi : ℂ)) ^ s ≠ 0 := fun h => by
    rw [cpow_eq_zero_iff] at h
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) h.1
  have hG : Gamma s ≠ 0 := by
    intro h0
    apply hs
    rw [Gammaℂ_def, h0]
    simp
  rw [ModularForm.L, CuspForm.Λ_eq_mellin]
  change moment f s = Gamma s / (2 * (Real.pi : ℂ)) ^ s * (moment f s * (2 / Gammaℂ s))
  rw [Gammaℂ_def, cpow_neg]
  field_simp

/-- **The completed `L`-value** `Λ(h, s) = (2π)^{-s} Γ(s) L(h, s)` of a level-one cusp form of weight `n + 2`, with `L` the entire
continuation of the Dirichlet series `∑ a_h(m) m^{-s}` (`ModularForm.L`). -/
def completedL (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) (s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-s) * Gamma s * ModularForm.L (weight_pos n) h s

theorem gammaℂ_ne_zero_nat (j : ℕ) : Gammaℂ ((j + 1 : ℕ) : ℂ) ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos ?_)
  · rw [Ne, cpow_eq_zero_iff]
    intro h
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) h.1
  · simpa using (show (0 : ℝ) < ((j + 1 : ℕ) : ℝ) by positivity)

theorem moment_eq_periodMoment' (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) (j : ℕ) :
    moment h ((j + 1 : ℕ) : ℂ) = periodMoment h j := by
  rw [moment_succ_eq_integral, periodMoment]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Set.mem_Ioi] at ht
  rw [imaginaryAxisValue, dite_eq_left ht,
    UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ)) (by simpa using ht)]
  ring

/-- **Moment = completed `L`-value at every critical integer**: `∫₀^∞ h(iy) y^j dy = Λ(h, j + 1)` for all `j` (in particular for the critical
integers `1, …, k - 1`, `j = 0, …, n`). -/
theorem periodMoment_eq_completedL (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) (j : ℕ) :
    periodMoment h j = completedL n h ((j + 1 : ℕ) : ℂ) := by
  rw [← moment_eq_periodMoment' n h j, moment_eq_gamma_mul_L h _ (gammaℂ_ne_zero_nat j), completedL,
    cpow_neg]
  field_simp

/-- **The contour integral at the critical integers**: `∫₀^{i∞} h(τ) τ^j dτ = i^{j+1} Λ(h, j+1)`, i.e.
`i^{j+1} Γ(j+1) (2π)^{-j-1} L(h, j+1)`, parametrizing `τ = it`, `dτ = i dt`. -/
theorem axis_integral_eq (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) (j : ℕ) :
    ∫ t : ℝ in Set.Ioi 0, h (ofComplex (Complex.I * t)) * (Complex.I * (t : ℂ)) ^ j * Complex.I =
      Complex.I ^ (j + 1) * completedL n h ((j + 1 : ℕ) : ℂ) := by
  have := axisMoment_eq (d := n) h j
  rw [axisMoment] at this
  rw [this, moment_eq_periodMoment' n h j, periodMoment_eq_completedL]

/-- **`eq:period-critical-coefficients`, literally**: the period polynomial of a level-one cusp form of weight `n + 2` is
`∑_{j=0}^n (-1)^{n-j} binom(n,j) i^{j+1} Λ(h, j+1) X^{n-j} Y^j`, with `Λ(h,s) = (2π)^{-s} Γ(s) L(h,s)`; the arguments `j + 1 = 1, …, n + 1 = k - 1`
are the critical integers. -/
theorem periodPolynomial_eq_critical (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) :
    periodPolynomial n h = ∑ j ∈ Finset.range (n + 1),
      C ((-1) ^ (n - j) * (n.choose j : ℂ) * Complex.I ^ (j + 1) * completedL n h ((j + 1 : ℕ) : ℂ)) *
        X 0 ^ (n - j) * X 1 ^ j := by
  rw [periodPolynomial]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (n.choose j : ℂ) * (-1) ^ (n - j) * Complex.I ^ (j + 1) * completedL n h ((j + 1 : ℕ) : ℂ) =
      (-1) ^ (n - j) * (n.choose j : ℂ) * Complex.I ^ (j + 1) * completedL n h ((j + 1 : ℕ) : ℂ) := by
    ring
  rw [periodMoment_eq_completedL, e]

/-- At a point of absolute convergence, `ModularForm.L` is the Dirichlet series `∑ a_h(m) m^{-s}` (generalizing
`TernaryPoly.BinaryCuspPeriod.lseries_eq_L`, the point `s = d`, to every `s` with `Re s > k/2 + 1`). -/
theorem lseries_eq_L_of_re {d : ℕ} (f : Forms d) (s : ℂ) (hs : ((d : ℝ) + 2) / 2 + 1 < s.re) :
    LSeries (coefficients f) s = ModularForm.L (weight_pos d) f s := by
  have hs' : (((d : ℤ) + 2 : ℤ) : ℝ) / 2 + 1 < s.re := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using hs
  have h := CuspForm.hasSum_L (weight_pos d) f hs'
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  simp only [ofReal_one, one_cpow, one_mul] at h
  have hd0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  simpa only [LSeries, LSeries.term_of_ne_zero' hd0, coefficients] using h.tsum_eq

/-- The completed `L`-value at a critical integer in the half-plane of absolute convergence is the completed Dirichlet series:
for `j > n/2 + 1`, `Λ(h, j+1) = (2π)^{-j-1} Γ(j+1) ∑_m a_h(m) m^{-j-1}`. -/
theorem completedL_eq_lseries (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) (j : ℕ)
    (hj : (n : ℝ) / 2 + 1 < j) :
    completedL n h ((j + 1 : ℕ) : ℂ) =
      (2 * (Real.pi : ℂ)) ^ (-((j + 1 : ℕ) : ℂ)) * Gamma ((j + 1 : ℕ) : ℂ) *
        LSeries (fourierCoeff h) ((j + 1 : ℕ) : ℂ) := by
  have hre : ((n : ℝ) + 2) / 2 + 1 < (((j + 1 : ℕ) : ℂ)).re := by
    have : (((j + 1 : ℕ) : ℂ)).re = (j : ℝ) + 1 := by simp
    rw [this]
    linarith
  have hc : fourierCoeff h = coefficients h := by
    funext m
    simp [fourierCoeff, coefficients, Subgroup.strictWidthInfty_SL2Z]
  rw [completedL, ← lseries_eq_L_of_re h _ hre, hc]

/-- The coefficient of `X^{n-j} Y^j` in `r_h`. -/
def criticalCoeff (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) (j : ℕ) : ℂ :=
  (-1) ^ (n - j) * (n.choose j : ℂ) * Complex.I ^ (j + 1) * completedL n h ((j + 1 : ℕ) : ℂ)

theorem bind_sign_term (c : ℂ) (a b : ℕ) :
    bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ) (C c * X 0 ^ a * X 1 ^ b) =
      C (c * (-1) ^ a) * X 0 ^ a * X 1 ^ b := by
  rw [map_mul, map_mul, bind₁_C_right, map_pow, map_pow, bind₁_X_right, bind₁_X_right]
  have : (-X 0 : MvPolynomial (Fin 2) ℂ) ^ a = C ((-1) ^ a) * X 0 ^ a := by
    rw [neg_pow, map_pow, map_neg, map_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [this, C_mul]
  ring

/-- **The parts of the period polynomial in `X` in terms of critical `L`-values**: `r_h^{ev}` carries the weights `(1 + (-1)^{n-j})/2` and
`r_h^{odd}` the weights `(1 - (-1)^{n-j})/2` on the coefficients `criticalCoeff`. For even `n`, `r_h^{ev}` involves only the odd critical
integers `s = j+1` (even `j`) and `r_h^{odd}` only the even ones. -/
theorem evenPeriodPart_eq_critical (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) :
    evenPeriodPart n h = ∑ j ∈ Finset.range (n + 1),
      C (((1 + (-1) ^ (n - j)) / 2 : ℂ) * criticalCoeff n h j) * X 0 ^ (n - j) * X 1 ^ j := by
  rw [evenPeriodPart, periodPolynomial_eq_critical, map_sum, smul_eq_C_mul, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bind_sign_term]
  have e : (C (2⁻¹ : ℂ) : MvPolynomial (Fin 2) ℂ) *
      (C (criticalCoeff n h j) * X 0 ^ (n - j) * X 1 ^ j +
        C (criticalCoeff n h j * (-1) ^ (n - j)) * X 0 ^ (n - j) * X 1 ^ j) =
      C (((1 + (-1) ^ (n - j)) / 2 : ℂ) * criticalCoeff n h j) * X 0 ^ (n - j) * X 1 ^ j := by
    have : (C ((1 + (-1) ^ (n - j)) / 2 * criticalCoeff n h j) : MvPolynomial (Fin 2) ℂ) =
        C (2⁻¹) * (C (criticalCoeff n h j) + C (criticalCoeff n h j * (-1) ^ (n - j))) := by
      rw [← map_add, ← C_mul]
      congr 1
      ring
    rw [this]
    ring
  exact e

/-- The odd part: weights `(1 - (-1)^{n-j})/2`. -/
theorem oddPeriodPart_eq_critical (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) :
    oddPeriodPart n h = ∑ j ∈ Finset.range (n + 1),
      C (((1 - (-1) ^ (n - j)) / 2 : ℂ) * criticalCoeff n h j) * X 0 ^ (n - j) * X 1 ^ j := by
  rw [oddPeriodPart, periodPolynomial_eq_critical, map_sum, smul_eq_C_mul, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bind_sign_term]
  have e : (C (2⁻¹ : ℂ) : MvPolynomial (Fin 2) ℂ) *
      (C (criticalCoeff n h j) * X 0 ^ (n - j) * X 1 ^ j -
        C (criticalCoeff n h j * (-1) ^ (n - j)) * X 0 ^ (n - j) * X 1 ^ j) =
      C (((1 - (-1) ^ (n - j)) / 2 : ℂ) * criticalCoeff n h j) * X 0 ^ (n - j) * X 1 ^ j := by
    have : (C ((1 - (-1) ^ (n - j)) / 2 * criticalCoeff n h j) : MvPolynomial (Fin 2) ℂ) =
        C (2⁻¹) * (C (criticalCoeff n h j) - C (criticalCoeff n h j * (-1) ^ (n - j))) := by
      rw [← map_sub, ← C_mul]
      congr 1
      ring
    rw [this]
    ring
  exact e

/-- **Functional equation of the completed `L`-value at the critical integers**: `Λ(h, n + 1 - j) = i^{n+2} Λ(h, j + 1)`, `0 ≤ j ≤ n`
(i.e. `Λ(h, k - s) = i^k Λ(h, s)`). -/
theorem completedL_reflection (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) {j : ℕ} (hj : j ≤ n) :
    completedL n h ((j + 1 : ℕ) : ℂ) = Complex.I ^ (n + 2) * completedL n h ((n - j + 1 : ℕ) : ℂ) := by
  rw [← periodMoment_eq_completedL, ← periodMoment_eq_completedL, ← moment_eq_periodMoment' n h,
    ← moment_eq_periodMoment' n h]
  exact moment_reflection h hj

/-- **The axis identity** (every `n`): `i Λ(h, 1) = - i^{n+1} Λ(h, n+1)`, i.e. the coefficients of `X^n` and `Y^n` of `r_h^{ev}` are opposite.
This is what makes the subtraction `r_h^{ev,0} = r_h^{ev} - r_h^{ev}(1,0)(X^n - Y^n)` of `eq:even-period-normalization` land on the axes:
`r_h^{ev,0}` vanishes on both (`TernaryPeriodPolynomials.Argument.Corollary14.normalizedEvenPeriodPart_axis_first`, `…_axis_second`). -/
theorem axis_identity (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) :
    Complex.I * completedL n h 1 = -(Complex.I ^ (n + 1) * completedL n h ((n + 1 : ℕ) : ℂ)) := by
  have h0 := completedL_reflection n h (Nat.zero_le n)
  rw [Nat.sub_zero] at h0
  have h1 : completedL n h ((0 + 1 : ℕ) : ℂ) = completedL n h 1 := by simp
  rw [h1] at h0
  rw [h0]
  have : Complex.I * Complex.I ^ (n + 2) = -Complex.I ^ (n + 1) := by
    rw [← pow_succ', show n + 2 + 1 = (n + 1) + 2 by ring, pow_add, Complex.I_sq]
    ring
  rw [← mul_assoc, this]
  ring

/-- `r_h^{ev}(1, 0) = i Λ(h, 1)` for even `n`: the quantity subtracted in `eq:even-period-normalization`. -/
theorem eval_evenPeriodPart_one_zero (n : ℕ) (hn : Even n) (h : CuspForm levelOne ((n : ℤ) + 2)) :
    eval ![1, 0] (evenPeriodPart n h) = Complex.I * completedL n h 1 := by
  rw [evenPeriodPart_eq_critical, map_sum, Finset.sum_eq_single 0]
  · simp only [map_mul, eval_C, map_pow, eval_X, Matrix.cons_val_zero, pow_zero, mul_one, criticalCoeff,
      Nat.sub_zero, hn.neg_one_pow, Nat.choose_zero_right, Nat.cast_one, zero_add, pow_one]
    have hw : (1 + (1 : ℂ)) / 2 = 1 := by norm_num
    simp [hw]
  · intro j _ hj0
    simp [zero_pow hj0]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

end TernaryPeriodPolynomials.Argument.CriticalValues
