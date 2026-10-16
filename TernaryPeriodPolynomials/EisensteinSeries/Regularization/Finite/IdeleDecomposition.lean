module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.Approximation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem integral_divisor_nat_associated (value : IntegralAdeles) (denominator : ℕ)
    (nonzero : denominator ≠ 0) (divides : value ∣ (denominator : IntegralAdeles))
    (unit_image : IsUnit (integralEmbedding value)) :
    ∃ factor : ℕ, factor ≠ 0 ∧ ∃ unit : IntegralAdelesˣ,
      value = (factor : IntegralAdeles) * unit.val := by
  obtain ⟨inverseFactor, product⟩ := divides
  obtain ⟨representative, remainder, residue⟩ :=
    integralAdeles_nat_decomposition denominator nonzero value
  let factor := Int.gcd (representative : ℤ) (denominator : ℤ)
  have factor_nonzero : factor ≠ 0 := by
    intro zero
    have denominator_zero := (Int.gcd_eq_zero_iff.mp zero).2
    exact nonzero (Int.ofNat_eq_zero.mp denominator_zero)
  obtain ⟨firstCoefficient, first_identity⟩ := Int.gcd_dvd_left (representative : ℤ) (denominator : ℤ)
  obtain ⟨secondCoefficient, second_identity⟩ := Int.gcd_dvd_right (representative : ℤ) (denominator : ℤ)
  have first_cast : (representative : IntegralAdeles) = (factor : IntegralAdeles) * firstCoefficient := by
    simpa only [factor, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun value : ℤ => (value : IntegralAdeles)) first_identity
  have second_cast : (denominator : IntegralAdeles) = (factor : IntegralAdeles) * secondCoefficient := by
    simpa only [factor, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun value : ℤ => (value : IntegralAdeles)) second_identity
  let quotient : IntegralAdeles := firstCoefficient + secondCoefficient * remainder
  have value_factor : value = (factor : IntegralAdeles) * quotient := by
    rw [residue, first_cast, second_cast]
    dsimp only [quotient]
    ring
  let bezout : IntegralAdeles :=
    (1 - inverseFactor * remainder) * (Int.gcdA representative denominator : ℤ) +
      inverseFactor * (Int.gcdB representative denominator : ℤ)
  have value_bezout : value * bezout = (factor : IntegralAdeles) := by
    have bezout_cast : (factor : IntegralAdeles) =
        (representative : IntegralAdeles) * (Int.gcdA representative denominator : ℤ) +
          (denominator : IntegralAdeles) * (Int.gcdB representative denominator : ℤ) := by
      simpa only [factor, Int.cast_mul, Int.cast_add, Int.cast_natCast] using
        congrArg (fun value : ℤ => (value : IntegralAdeles))
          (Int.gcd_eq_gcd_ab (representative : ℤ) (denominator : ℤ))
    rw [bezout_cast]
    have value_representative : value * (1 - inverseFactor * remainder) = representative := by
      rw [mul_sub, mul_one, ← mul_assoc, ← product, residue]
      ring
    calc
      _ = (value * (1 - inverseFactor * remainder)) * (Int.gcdA representative denominator : ℤ) +
          (value * inverseFactor) * (Int.gcdB representative denominator : ℤ) := by dsimp [bezout]; ring
      _ = _ := by rw [value_representative, ← product]
  have quotient_inverse : quotient * bezout = 1 := by
    apply integralEmbedding_injective
    apply unit_image.mul_left_cancel
    rw [← map_mul, ← map_mul]
    congr 1
    calc
      value * (quotient * bezout) = (value * bezout) * quotient := by ring
      _ = (factor : IntegralAdeles) * quotient := by rw [value_bezout]
      _ = value * 1 := by rw [← value_factor, mul_one]
  refine ⟨factor, factor_nonzero, ⟨quotient, bezout, quotient_inverse, ?_⟩, value_factor⟩
  simpa only [mul_comm] using quotient_inverse

theorem finiteIdele_rational_integral_decomposition (idele : FiniteAdelesˣ) :
    ∃ rational : ℚˣ, 0 < rational.val ∧ ∃ integralUnit : IntegralAdelesˣ,
      idele = Units.map (algebraMap ℚ FiniteAdeles) rational * Units.map integralEmbedding integralUnit := by
  obtain ⟨denominator, numerator, denominator_nonzero, numerator_spec⟩ := finiteAdele_nat_denominator idele.val
  obtain ⟨inverseDenominator, inverseNumerator, inverse_nonzero, inverse_spec⟩ :=
    finiteAdele_nat_denominator (idele⁻¹).val
  have denominator_unit : IsUnit (denominator : FiniteAdeles) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr denominator_nonzero : (denominator : ℚ) ≠ 0)).map
        (algebraMap ℚ FiniteAdeles)
  have numerator_unit : IsUnit (integralEmbedding numerator) := by
    rw [numerator_spec]
    exact denominator_unit.mul idele.isUnit
  have integral_product : (denominator * inverseDenominator : ℕ) = numerator * inverseNumerator := by
    apply integralEmbedding_injective
    rw [map_natCast, Nat.cast_mul, map_mul, numerator_spec, inverse_spec]
    calc
      _ = ((denominator : FiniteAdeles) * inverseDenominator) * (idele.val * (idele⁻¹).val) := by simp
      _ = _ := by ring
  obtain ⟨factor, factor_nonzero, integralUnit, factorization⟩ :=
    integral_divisor_nat_associated numerator (denominator * inverseDenominator)
      (mul_ne_zero denominator_nonzero inverse_nonzero) ⟨inverseNumerator, integral_product⟩ numerator_unit
  have rational_positive : 0 < (factor : ℚ) / denominator :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero factor_nonzero))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero denominator_nonzero))
  have rational_cancel : (denominator : FiniteAdeles) *
      algebraMap ℚ FiniteAdeles ((factor : ℚ) / denominator) = factor := by
    rw [← map_natCast (algebraMap ℚ FiniteAdeles) denominator, ← map_mul]
    have cancel : (denominator : ℚ) * ((factor : ℚ) / denominator) = factor := by field_simp
    rw [cancel, map_natCast]
  refine ⟨Units.mk0 ((factor : ℚ) / denominator) rational_positive.ne', rational_positive, integralUnit, ?_⟩
  apply Units.ext
  apply denominator_unit.mul_left_cancel
  change (denominator : FiniteAdeles) * idele.val =
    (denominator : FiniteAdeles) * (algebraMap ℚ FiniteAdeles ((factor : ℚ) / denominator) * integralEmbedding integralUnit.val)
  rw [← numerator_spec, factorization, map_mul, map_natCast, ← mul_assoc, rational_cancel]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
