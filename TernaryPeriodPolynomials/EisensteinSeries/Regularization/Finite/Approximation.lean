module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.Congruences

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem local_nat_denominator (place : FinitePlace) (value : place.adicCompletion ℚ) :
    ∃ denominator : ℕ, denominator ≠ 0 ∧
      (denominator : place.adicCompletion ℚ) * value ∈ place.adicCompletionIntegers ℚ := by
  let prime := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)) place
  let : Fact prime.val.Prime := ⟨prime.property⟩
  let padicValue := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place) value
  have positive : 0 < ‖padicValue‖ + 1 := by positivity
  obtain ⟨power, power_small⟩ :=
    PadicInt.exists_pow_neg_lt prime.val (show 0 < 1 / (‖padicValue‖ + 1) by positivity)
  have norm_bound : ‖(prime.val : ℚ_[prime.val]) ^ power * padicValue‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow]
    have product_lt := (lt_div_iff₀ positive).mp power_small
    have power_nonnegative : 0 ≤ (prime.val : ℝ) ^ (-(power : ℤ)) := by positivity
    nlinarith
  refine ⟨prime.val ^ power, pow_ne_zero _ prime.property.ne_zero, ?_⟩
  have mapped_integral :
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place)
        ((prime.val ^ power : ℕ) * value) ∈ PadicInt.subring prime.val := by
    rw [PadicInt.mem_subring_iff]
    simpa only [map_mul, map_natCast, Nat.cast_pow, map_pow] using norm_bound
  obtain ⟨preimage, preimage_integral, same_image⟩ :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn place).surjOn mapped_integral
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place).injective same_image ▸
    preimage_integral

theorem finiteAdele_nat_denominator (value : FiniteAdeles) :
    ∃ (denominator : ℕ) (integralValue : IntegralAdeles),
      denominator ≠ 0 ∧ integralEmbedding integralValue = (denominator : FiniteAdeles) * value := by
  classical
  have finite_bad := Filter.eventually_cofinite.mp value.property
  let badPlaces := finite_bad.toFinset
  choose localDenominator denominator_nonzero denominator_integral using
    (fun place : FinitePlace => local_nat_denominator place (value place))
  let denominator := ∏ place ∈ badPlaces, localDenominator place
  have common_integral (place : FinitePlace) :
      (denominator : place.adicCompletion ℚ) * value place ∈ place.adicCompletionIntegers ℚ := by
    by_cases bad : place ∈ badPlaces
    · obtain ⟨multiplier, product_spec⟩ := Finset.dvd_prod_of_mem localDenominator bad
      have integral_product := (place.adicCompletionIntegers ℚ).toSubring.mul_mem
        (natCast_mem (place.adicCompletionIntegers ℚ).toSubring multiplier) (denominator_integral place)
      change denominator = localDenominator place * multiplier at product_spec
      rw [product_spec, Nat.cast_mul]
      rw [mul_comm (localDenominator place : place.adicCompletion ℚ), mul_assoc]
      exact integral_product
    · have value_integral : value place ∈ place.adicCompletionIntegers ℚ := by
        have not_bad := bad
        simp only [badPlaces, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at not_bad
        exact not_bad
      exact (place.adicCompletionIntegers ℚ).toSubring.mul_mem
        (natCast_mem (place.adicCompletionIntegers ℚ).toSubring denominator) value_integral
  refine ⟨denominator, fun place => ⟨_, common_integral place⟩, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun place _ => denominator_nonzero place)
  · ext place
    rfl

theorem finiteAdele_rational_approximation (value : FiniteAdeles) :
    ∃ (rational : ℚ) (integralValue : IntegralAdeles),
      value - algebraMap ℚ FiniteAdeles rational = integralEmbedding integralValue := by
  obtain ⟨denominator, numerator, denominator_nonzero, numerator_spec⟩ :=
    finiteAdele_nat_denominator value
  obtain ⟨representative, quotient, decomposition⟩ :=
    integralAdeles_nat_decomposition denominator denominator_nonzero numerator
  have denominator_rational_nonzero : (denominator : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr denominator_nonzero
  have denominator_unit : IsUnit (denominator : FiniteAdeles) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr denominator_rational_nonzero).map (algebraMap ℚ FiniteAdeles)
  have finite_decomposition : (denominator : FiniteAdeles) * value =
      representative + (denominator : FiniteAdeles) * integralEmbedding quotient := by
    rw [← numerator_spec, decomposition]
    simp only [map_add, map_mul, map_natCast]
  have quotient_cancel : (denominator : FiniteAdeles) *
      algebraMap ℚ FiniteAdeles ((representative : ℚ) / denominator) = representative := by
    rw [← map_natCast (algebraMap ℚ FiniteAdeles) denominator, ← map_mul]
    have cancel : (denominator : ℚ) * ((representative : ℚ) / denominator) = representative := by
      field_simp
    rw [cancel, map_natCast]
  refine ⟨(representative : ℚ) / denominator, quotient, denominator_unit.mul_left_cancel ?_⟩
  rw [mul_sub, quotient_cancel, finite_decomposition]
  abel

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
