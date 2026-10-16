module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodPolynomial
public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.BinaryCuspOuter

@[expose] public section


/-!
# Corollary 1.4, Step 1: the cusp-period-polynomial bridge

Bridges `SphericalDetection.Helpers.cuspPeriodPolynomial`/`cuspImaginaryMoment` (the moment-based
period polynomial feeding the cohomological Eichler-Shimura machinery in `AxiomCodeSpectral`) to
`TernaryPeriodPolynomials.Argument.periodPolynomial`/`periodMoment`, for even degree.

Both moments are literally the same `Ioi 0` integral up to argument order
(`cuspImaginaryMoment_eq_periodMoment`); no analytic machinery (no `mellin`, no FTC along the
imaginary axis) is needed, unlike the harder, unrelated bridge to
`TernaryPoly.BinaryCuspPeriod.moment`/`period`.
The polynomials then match coefficientwise because `(-I)^j * I = (-1)^j * I^(j+1)` and, for even
`degree`, `(-1)^(degree-j) = (-1)^j` (`cuspPeriodPolynomial_eq_periodPolynomial`).
-/

noncomputable section
open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein.Binary (HomogeneousPoly Poly)
open TernaryPoly.BinaryCuspPeriod (Forms)

/-- The two moment integrals are the same `Ioi 0` integral, up to multiplication order. -/
theorem cuspImaginaryMoment_eq_periodMoment {d : ℕ} (f : Forms d) (j : ℕ) :
    cuspImaginaryMoment f j = TernaryPeriodPolynomials.Argument.periodMoment f j := by
  rw [cuspImaginaryMoment, TernaryPeriodPolynomials.Argument.periodMoment]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Set.mem_Ioi] at ht
  rw [TernaryPeriodPolynomials.Argument.imaginaryAxisValue, dite_eq_left ht,
    UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ)) (by simpa using ht)]
  ring

/-- For even `d` and `j ≤ d`, `(-1) ^ (d - j) = (-1) ^ j` in `ℂ`. -/
private theorem sign_sub_eq_of_even {d : ℕ} (hd : Even d) {j : ℕ} (hj : j ≤ d) :
    (-1 : ℂ) ^ (d - j) = (-1 : ℂ) ^ j := by
  rcases Nat.even_or_odd j with hj' | hj'
  · have hdj : Even (d - j) := by
      obtain ⟨c, hc⟩ := hd
      obtain ⟨c', hc'⟩ := hj'
      exact ⟨c - c', by omega⟩
    rw [hj'.neg_one_pow, hdj.neg_one_pow]
  · have hdj : Odd (d - j) := by
      obtain ⟨c, hc⟩ := hd
      obtain ⟨c', hc'⟩ := hj'
      exact ⟨c - c' - 1, by omega⟩
    rw [hj'.neg_one_pow, hdj.neg_one_pow]

/-- `(-I)^j * I = (-1)^j * I^(j+1)`, the sign/power identity turning
`cuspPeriodPolynomial`'s coefficients into `periodPolynomial`'s. -/
private theorem neg_I_pow_mul_I (j : ℕ) :
    (-Complex.I) ^ j * Complex.I = (-1 : ℂ) ^ j * Complex.I ^ (j + 1) := by
  have hsplit : (-Complex.I : ℂ) = (-1) * Complex.I := by ring
  rw [hsplit, mul_pow, pow_succ]
  ring

/-- The scalar coefficient of `cuspPeriodPolynomial`'s basis expansion at position `d - j`
equals `periodPolynomial`'s coefficient at `j`, for even `d` and `j ≤ d`. -/
private theorem cusp_coeff_eq {d : ℕ} (hd : Even d) (f : Forms d) {j : ℕ} (hj : j ≤ d) :
    ((d.choose (d - j) : ℕ) : ℂ) * (-Complex.I) ^ (d - (d - j)) * Complex.I *
        cuspImaginaryMoment f (d - (d - j)) =
      (d.choose j : ℂ) * (-1) ^ (d - j) * Complex.I ^ (j + 1) *
        TernaryPeriodPolynomials.Argument.periodMoment f j := by
  have e1 : d - (d - j) = j := by omega
  rw [e1, Nat.choose_symm hj, cuspImaginaryMoment_eq_periodMoment, sign_sub_eq_of_even hd hj]
  have hpow := neg_I_pow_mul_I j
  linear_combination TernaryPeriodPolynomials.Argument.periodMoment f j * hpow

/-- **Plan step 1.** `cuspPeriodPolynomial` and `periodPolynomial` agree as elements of
`MvPolynomial (Fin 2) ℂ`, for even degree. -/
theorem cuspPeriodPolynomial_eq_periodPolynomial {d : ℕ} (hd : Even d) (f : Forms d) :
    (cuspPeriodPolynomial f d : Poly) = TernaryPeriodPolynomials.Argument.periodPolynomial d f := by
  have hcoe : (cuspPeriodPolynomial f d : Poly) =
      ∑ p ∈ Finset.range (d + 1),
        (((d.choose p : ℕ) : ℂ) * (-Complex.I) ^ (d - p) * Complex.I *
            cuspImaginaryMoment f (d - p)) • (X 0 ^ p * X 1 ^ (d - p) : Poly) := by
    have hfin : (cuspPeriodPolynomial f d : Poly) =
        ∑ x : Fin (d + 1),
          (((d.choose (x : ℕ) : ℕ) : ℂ) * (-Complex.I) ^ (d - (x : ℕ)) * Complex.I *
              cuspImaginaryMoment f (d - (x : ℕ))) •
            (X 0 ^ (x : ℕ) * X 1 ^ (d - (x : ℕ)) : Poly) := by
      simp [cuspPeriodPolynomial, binaryStandardBasis_coe]
    rw [hfin, Fin.sum_univ_eq_sum_range (fun p =>
      (((d.choose p : ℕ) : ℂ) * (-Complex.I) ^ (d - p) * Complex.I *
        cuspImaginaryMoment f (d - p)) • (X 0 ^ p * X 1 ^ (d - p) : Poly)) (d + 1)]
  rw [hcoe, TernaryPeriodPolynomials.Argument.periodPolynomial,
    ← Finset.sum_range_reflect (fun p =>
      (((d.choose p : ℕ) : ℂ) * (-Complex.I) ^ (d - p) * Complex.I *
        cuspImaginaryMoment f (d - p)) • (X 0 ^ p * X 1 ^ (d - p) : Poly)) (d + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjd : j ≤ d := by omega
  have e2 : d - (d - j) = j := by omega
  show (((d.choose (d - j) : ℕ) : ℂ) * (-Complex.I) ^ (d - (d - j)) * Complex.I *
      cuspImaginaryMoment f (d - (d - j))) • (X 0 ^ (d - j) * X 1 ^ (d - (d - j)) : Poly) =
    C ((d.choose j : ℂ) * (-1) ^ (d - j) * Complex.I ^ (j + 1) *
        TernaryPeriodPolynomials.Argument.periodMoment f j) * X 0 ^ (d - j) * X 1 ^ j
  rw [cusp_coeff_eq hd f hjd, e2, MvPolynomial.smul_eq_C_mul]
  ring

end TernaryPeriodPolynomials.Argument.Corollary14
