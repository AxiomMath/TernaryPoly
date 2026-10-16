module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePositiveTruncation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def positiveEulerMajorant (exponent : ℂ) (place : FinitePlace) : ℝ :=
  ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ) ^ (2 - exponent.re)

theorem positiveEulerMajorant_nonneg (exponent : ℂ) (place : FinitePlace) :
    0 ≤ positiveEulerMajorant exponent place := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem positiveEulerMajorant_small (exponent : ℂ) (convergent : 3 < exponent.re) (place : FinitePlace) :
    positiveEulerMajorant exponent place ≤ 1 / 2 := by
  have prime_large : (2 : ℝ) ≤ (Rat.HeightOneSpectrum.primesEquiv place).val := by
    exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv place).property.two_le
  calc
    _ ≤ ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) prime_large

theorem positiveEulerMajorant_summable (exponent : ℂ) (convergent : 3 < exponent.re) :
    Summable (positiveEulerMajorant exponent) := by
  have summable : Summable (fun place : Nat.Primes => (place.val : ℝ) ^ (2 - exponent.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  exact summable.comp_injective Rat.HeightOneSpectrum.primesEquiv.injective

theorem inverse_one_sub_le_exp (value : ℝ) (nonnegative : 0 ≤ value) (small : value ≤ 1 / 2) :
    (1 - value)⁻¹ ≤ Real.exp (2 * value) := by
  have positive : 0 < 1 - value := by linarith
  have rational_bound : (1 - value)⁻¹ ≤ 1 + 2 * value := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ positive).mpr
    nlinarith
  exact rational_bound.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * value))

theorem padicPositiveWeight_integral_le_exp (exponent : ℂ) (convergent : 3 < exponent.re) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (∫ pair, padicPositiveWeight exponent pair ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) ≤
      Real.exp (2 * positiveEulerMajorant exponent place) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have equality : Real.exp ((2 - exponent.re) * Real.log (Rat.HeightOneSpectrum.primesEquiv place).val) =
      positiveEulerMajorant exponent place := by
    rw [positiveEulerMajorant, Real.rpow_def_of_pos (by exact_mod_cast
      (Rat.HeightOneSpectrum.primesEquiv place).property.pos)]
    rw [mul_comm]
  have bound := padicPositiveWeight_integral_le (finitePadicMeasure place) (finitePadicMeasure_normalized place)
    exponent (by linarith)
  rw [equality] at bound
  exact bound.trans (inverse_one_sub_le_exp _ (positiveEulerMajorant_nonneg exponent place)
    (positiveEulerMajorant_small exponent convergent place))

theorem goodLinePositiveWeight_truncated_bound (exponent : ℂ) (convergent : 3 < exponent.re)
    (places : Finset FinitePlace) :
    (∫ pair in goodLineFiniteSupportRegion places, goodLinePositiveWeight exponent pair
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) ≤
      Real.exp (2 * ∑ place ∈ places, positiveEulerMajorant exponent place) := by
  classical
  induction places using Finset.induction_on with
  | empty => rw [goodLinePositiveWeight_empty_integral, Finset.sum_empty, mul_zero, Real.exp_zero]
  | @insert place places outside induction =>
      rw [Finset.sum_insert outside, mul_add, Real.exp_add]
      by_cases same : place = placeThree
      · subst place
        rw [goodLineFiniteSupportRegion_insert_three]
        exact induction.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (Real.one_le_exp
          (mul_nonneg (by norm_num) (positiveEulerMajorant_nonneg exponent placeThree))))
      · rw [goodLinePositiveWeight_insert_integral exponent places place same outside]
        exact mul_le_mul (padicPositiveWeight_integral_le_exp exponent convergent place) induction
          (integral_nonneg (goodLinePositiveWeight_nonneg exponent)) (Real.exp_nonneg _)

theorem goodLinePositiveWeight_uniform_bound (exponent : ℂ) (convergent : 3 < exponent.re)
    (places : Finset FinitePlace) :
    (∫ pair in goodLineFiniteSupportRegion places, goodLinePositiveWeight exponent pair
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) ≤
      Real.exp (2 * ∑' place, positiveEulerMajorant exponent place) := by
  apply (goodLinePositiveWeight_truncated_bound exponent convergent places).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    ((positiveEulerMajorant_summable exponent convergent).sum_le_tsum places
      (fun place _ => positiveEulerMajorant_nonneg exponent place)) (by norm_num)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
