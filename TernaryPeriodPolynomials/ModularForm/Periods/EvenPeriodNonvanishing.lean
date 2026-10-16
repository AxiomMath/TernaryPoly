module

public import TernaryPeriodPolynomials.ModularForm.BinaryCuspOuter
public import TernaryPeriodPolynomials.ModularForm.Period.Hecke
public import TernaryPeriodPolynomials.ModularForm.HeckeLSeries.LSeries
public import TernaryPeriodPolynomials.ModularForm.Hecke.Eigen
public import TernaryPeriodPolynomials.ModularForm.Period.Injective
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenCuspBridge
public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodSmul
public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodTenDimension

@[expose] public section



/-!
# Nonvanishing of `normalizedEvenPeriodPart 10 h` for `h ≠ 0`

Mirrors the odd/symmetric nonvanishing argument of `ExampleDegreeTenCuspBridge.lean`
(`oddPeriodPart_ne_zero_of_ne_zero`) on the even side. `Forms 10` is one-dimensional
(`forms_ten_finrank_eq_one`), so any nonzero `h : Forms 10` is, after rescaling by its first
Fourier coefficient, a simultaneous prime-Hecke eigenform `g` with `coefficients g 1 = 1`. For
such a normalized eigenform, `periodCoefficient g 2 ≠ 0` follows from the Euler product /
L-series nonvanishing at the edge point `s = 9` (`TernaryPoly.BinaryHeckeEulerProduct`), via the
Mellin-transform identification of `periodCoefficient g 2` with `L(g, 9)` up to an explicit
nonzero scalar. The coefficient-two Fourier coefficient of `normalizedEvenPeriodPart 10 g` is
exactly `periodCoefficient g 2` (the axis-monomial correction `X 0 ^ 10 - X 1 ^ 10` does not
contribute at that exponent), so `normalizedEvenPeriodPart 10 g ≠ 0`; scaling back by the
(nonzero) first Fourier coefficient of `h` transports this to `h` itself, via
`normalizedEvenPeriodPart_smul`.
-/

noncomputable section
open Complex MvPolynomial
open scoped MatrixGroups

namespace TernaryPeriodPolynomials.Argument.CuspForms

open TernaryPoly.BinaryCuspPeriod

theorem lseries_summable_nine (f : Forms 10) :
    LSeriesSummable (coefficients f) (9 : ℂ) := by
  apply LSeriesSummable_of_isBigO_rpow (x := ((10 : ℝ) + 2) / 2 + 1)
  · norm_num
  · simpa using coefficient_growth f

theorem lseries_eq_L_nine (f : Forms 10) :
    LSeries (coefficients f) (9 : ℂ) = ModularForm.L (weight_pos 10) f (9 : ℂ) := by
  have hs : (((10 : ℤ) + 2 : ℤ) : ℝ) / 2 + 1 < (9 : ℂ).re := by norm_num
  have h := CuspForm.hasSum_L (weight_pos 10) f hs
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  simp only [ofReal_one, one_cpow, one_mul] at h
  have hd0 : (9 : ℂ) ≠ 0 := by norm_num
  simpa only [LSeries, LSeries.term_of_ne_zero' hd0, coefficients] using h.tsum_eq

theorem moment_nine_eq (f : Forms 10) :
    moment f (9 : ℂ) = Gamma (9 : ℂ) / (2 * (Real.pi : ℂ)) ^ (9:ℕ) *
      ModularForm.L (weight_pos 10) f (9 : ℂ) := by
  have hg : Gamma (9 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hp : (2 * (Real.pi : ℂ)) ^ (9:ℕ) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hcpow : ((2:ℂ) * (Real.pi:ℂ)) ^ (9:ℂ) = ((2:ℂ) * (Real.pi:ℂ)) ^ (9:ℕ) := by
    rw [show (9:ℂ) = ((9:ℕ):ℂ) by norm_num, cpow_natCast]
  rw [ModularForm.L, CuspForm.Λ_eq_mellin]
  change moment f (9 : ℂ) = Gamma (9 : ℂ) / (2 * (Real.pi : ℂ)) ^ (9:ℕ) *
    (moment f (9 : ℂ) * (2 / Gammaℂ (9 : ℂ)))
  rw [Gammaℂ_def, cpow_neg, hcpow]
  field_simp

open TernaryPoly.BinaryCuspHecke
open TernaryPoly.BinaryCuspPeriodInjective

theorem periodCoefficient_two_eq_L (f : Forms 10) :
    periodCoefficient f 2 =
      (Nat.choose 10 2 : ℂ) * I ^ 9 * Gamma (9 : ℂ) / (2 * (Real.pi : ℂ)) ^ (9:ℕ) *
        LSeries (coefficients f) (9 : ℂ) := by
  have hunfold : periodCoefficient f 2 =
      (Nat.choose 10 2 : ℂ) * (-1)^2 * I ^ 9 * moment f (9:ℂ) := by
    unfold periodCoefficient
    norm_num
  rw [hunfold, moment_nine_eq, lseries_eq_L_nine]
  ring

theorem scalar_two_ne_zero :
    (Nat.choose 10 2 : ℂ) * I ^ 9 * Gamma (9 : ℂ) / (2 * (Real.pi : ℂ)) ^ (9:ℕ) ≠ 0 := by
  have hchoose : (Nat.choose 10 2 : ℂ) ≠ 0 := by
    have hnat : Nat.choose 10 2 ≠ 0 := (Nat.choose_pos (by norm_num)).ne'
    exact_mod_cast hnat
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero hchoose (pow_ne_zero _ I_ne_zero))
      (Gamma_ne_zero_of_re_pos (by norm_num))
  · exact pow_ne_zero _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))

theorem isPrimeEigenform_smul {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ)
    (hf : IsPrimeEigenform f ev) (c : ℂ) :
    IsPrimeEigenform (c • f) ev := by
  rw [isPrimeEigenform_iff] at hf ⊢
  intro p
  rw [map_smul, hf p, smul_smul, mul_comm, ← smul_smul]

theorem exists_eigenvalue_ten {h : Forms 10} (hh0 : h ≠ 0) :
    ∃ ev : Nat.Primes → ℂ, IsPrimeEigenform h ev := by
  have hspan : (ℂ ∙ h) = ⊤ :=
    (finrank_eq_one_iff_of_nonzero h hh0).mp forms_ten_finrank_eq_one
  have hex : ∀ p : Nat.Primes, ∃ c : ℂ, primeHecke 10 p h = c • h := by
    intro p
    have hmem : primeHecke 10 p h ∈ ℂ ∙ h := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  refine ⟨fun p => Classical.choose (hex p), ?_⟩
  rw [isPrimeEigenform_iff]
  intro p
  exact Classical.choose_spec (hex p)

theorem lseries_nine_ne_zero {g : Forms 10} (ev : Nat.Primes → ℂ)
    (hg : IsPrimeEigenform g ev) (hg1 : coefficients g 1 = 1) :
    LSeries (coefficients g) (9 : ℂ) ≠ 0 := by
  have h9 : ((9:ℕ):ℂ) = (9:ℂ) := by norm_num
  have hs : LSeriesSummable (coefficients g) ((9:ℕ):ℂ) := by
    rw [h9]; exact lseries_summable_nine g
  have hL := TernaryPoly.BinaryHeckeEulerProduct.LSeries_nat_ne_zero (coefficients g)
    (fun p => (p.val:ℂ)^(10+1)) 9
    (coefficients_zero g) hg1
    (eigen_coefficients_multiplicative g ev hg hg1)
    (eigen_coefficients_prime_recurrence g ev hg hg1) hs
  rwa [h9] at hL

theorem periodCoefficient_two_ne_zero_of_eigen {g : Forms 10} (ev : Nat.Primes → ℂ)
    (hg : IsPrimeEigenform g ev) (hg1 : coefficients g 1 = 1) :
    periodCoefficient g 2 ≠ 0 := by
  rw [periodCoefficient_two_eq_L]
  exact mul_ne_zero scalar_two_ne_zero (lseries_nine_ne_zero ev hg hg1)

theorem coeff_evenPeriod_two (g : Forms 10) :
    (evenPeriod g).coeff (exponent 10 2) = periodCoefficient g 2 := by
  rw [evenPeriod, MvPolynomial.smul_eq_C_mul, coeff_C_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_bind1_signflip, exponent_zero, coeff_period g (by norm_num : (2:ℕ) ≤ 10)]
  ring

theorem coeff_exponent_two_axisMonomial :
    (X 0 ^ 10 - X 1 ^ 10 : MvPolynomial (Fin 2) ℂ).coeff (exponent 10 2) = 0 := by
  have h0 : exponent 10 2 ≠ Finsupp.single (0:Fin 2) 10 := by
    intro h
    have := congrArg (fun m => m 0) h
    simp [exponent_zero] at this
  have h1 : exponent 10 2 ≠ Finsupp.single (1:Fin 2) 10 := by
    intro h
    have := congrArg (fun m => m 1) h
    simp [exponent_one] at this
  simp [coeff_X_pow, h0.symm, h1.symm]

theorem normalizedEvenPeriodPart_ne_zero_of_eigen {g : Forms 10} (ev : Nat.Primes → ℂ)
    (hg : IsPrimeEigenform g ev) (hg1 : coefficients g 1 = 1) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 g ≠ 0 := by
  have hne2 : periodCoefficient g 2 ≠ 0 := periodCoefficient_two_ne_zero_of_eigen ev hg hg1
  have hcoeff : (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 g).coeff (exponent 10 2) ≠ 0 := by
    rw [TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart, coeff_sub,
      coeff_C_mul, coeff_exponent_two_axisMonomial, mul_zero, sub_zero,
      ← evenPeriod_eq_evenPeriodPart, coeff_evenPeriod_two]
    exact hne2
  intro h
  rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  exact hcoeff rfl

/-- For `h : Forms 10 = CuspForm levelOne 12` nonzero, `normalizedEvenPeriodPart 10 h ≠ 0`. The
even-side analogue of `oddPeriodPart_ne_zero_of_ne_zero`. -/
theorem normalizedEvenPeriodPart_ne_zero_of_ne_zero_ten {h : Forms 10} (hh0 : h ≠ 0) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 h ≠ 0 := by
  obtain ⟨ev, hev⟩ := exists_eigenvalue_ten hh0
  have h1ne : coefficients h 1 ≠ 0 := first_coefficient_ne_zero h ev hev hh0
  set g : Forms 10 := (coefficients h 1)⁻¹ • h with hg_def
  have hgev : IsPrimeEigenform g ev := isPrimeEigenform_smul h ev hev _
  have hg1 : coefficients g 1 = 1 := by
    rw [hg_def, coefficients_smul, inv_mul_cancel₀ h1ne]
  have hgne : TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 g ≠ 0 :=
    normalizedEvenPeriodPart_ne_zero_of_eigen ev hgev hg1
  have hhg : h = (coefficients h 1) • g := by
    rw [hg_def, smul_smul, mul_inv_cancel₀ h1ne, one_smul]
  rw [hhg, normalizedEvenPeriodPart_smul]
  exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr h1ne) hgne

end TernaryPeriodPolynomials.Argument.CuspForms
