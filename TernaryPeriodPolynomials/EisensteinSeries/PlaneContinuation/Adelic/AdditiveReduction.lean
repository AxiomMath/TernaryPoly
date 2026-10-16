module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.Denominators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicAdditiveReduction

theorem integral_residue (modulus : ℕ) (nonzero : modulus ≠ 0) (value : IntegralAdeles) :
    ∃ residue : ℕ, ∃ quotient : IntegralAdeles, (residue : IntegralAdeles) + modulus * quotient = value := by
  induction modulus using Nat.recOnMul generalizing value with
  | zero => exact (nonzero rfl).elim
  | one => exact ⟨0, value, by simp⟩
  | prime prime primeProperty =>
    let place : FinitePlace := Rat.HeightOneSpectrum.primesEquiv.symm ⟨prime, primeProperty⟩
    obtain ⟨quotient, equality⟩ := Residue.exists_residue_quotient place value
    refine ⟨(Residue.reduction place value).val, quotient, ?_⟩
    have primeEquality : (Rat.HeightOneSpectrum.primesEquiv place).val = prime :=
      congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨prime, primeProperty⟩)
    exact (congrArg (fun integer : ℕ => ((Residue.reduction place value).val : IntegralAdeles) +
      integer * quotient) primeEquality).symm.trans equality
  | mul first second firstHypothesis secondHypothesis =>
    obtain ⟨firstResidue, firstQuotient, firstEquality⟩ :=
      firstHypothesis (mul_ne_zero_iff.mp nonzero).1 value
    obtain ⟨secondResidue, quotient, secondEquality⟩ :=
      secondHypothesis (mul_ne_zero_iff.mp nonzero).2 firstQuotient
    refine ⟨firstResidue + first * secondResidue, quotient, ?_⟩
    rw [← firstEquality, ← secondEquality]
    push_cast
    ring

theorem exists_rational_add_integral (value : FiniteAdeles) :
    ∃ rational : ℚ, ∃ integral : IntegralAdeles,
      value = algebraMap ℚ FiniteAdeles rational + integralEmbedding integral := by
  obtain ⟨denominator, nonzero, integral, integralEquality⟩ :=
    AdelicDenominators.exists_nat_denominator value
  obtain ⟨residue, quotient, quotientEquality⟩ := integral_residue denominator nonzero integral
  refine ⟨(residue : ℚ) / denominator, quotient, ?_⟩
  have denominatorNonzero : (denominator : ℚ) ≠ 0 := by exact_mod_cast nonzero
  have denominatorUnit : IsUnit (denominator : FiniteAdeles) := by
    simpa using (isUnit_iff_ne_zero.mpr denominatorNonzero).map (algebraMap ℚ FiniteAdeles)
  apply denominatorUnit.mul_left_cancel
  have rationalProduct : (denominator : FiniteAdeles) *
      algebraMap ℚ FiniteAdeles ((residue : ℚ) / denominator) = residue := by
    rw [← map_natCast (algebraMap ℚ FiniteAdeles) denominator, ← map_mul]
    have cancellation : (denominator : ℚ) * ((residue : ℚ) / denominator) = residue := by
      field_simp
    rw [cancellation, map_natCast]
  rw [mul_add, rationalProduct, ← integralEquality, ← quotientEquality, map_add, map_mul, map_natCast, map_natCast]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicAdditiveReduction
