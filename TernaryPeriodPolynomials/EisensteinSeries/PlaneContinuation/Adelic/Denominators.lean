module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Residue

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicDenominators

theorem padic_clear_denominator {prime : ℕ} [Fact prime.Prime] (value : ℚ_[prime]) :
    ∃ exponent : ℕ, ‖(prime : ℚ_[prime]) ^ exponent * value‖ ≤ 1 := by
  obtain ⟨exponent, bound⟩ := PadicInt.exists_pow_neg_lt prime
    (show 0 < (‖value‖ + 1)⁻¹ by positivity)
  refine ⟨exponent, ?_⟩
  rw [norm_mul, Padic.norm_p_pow]
  have powerNonnegative : 0 ≤ (prime : ℝ) ^ (-(exponent : ℤ)) := by positivity
  have productBound : (prime : ℝ) ^ (-(exponent : ℤ)) * (‖value‖ + 1) < 1 := by
    exact (lt_div_iff₀ (by positivity : 0 < ‖value‖ + 1)).mp (by simpa only [one_div] using bound)
  nlinarith

theorem local_integral_iff_norm (place : FinitePlace) (value : place.adicCompletion ℚ) :
    let _ : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    value ∈ place.adicCompletionIntegers ℚ ↔
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv place value‖ ≤ 1 := by
  let _ : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  constructor
  · intro membership
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn place).mapsTo membership
  · intro bound
    obtain ⟨preimage, membership, equality⟩ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn place).surjOn bound
    have equalValues := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place).injective equality
    rwa [← equalValues]

theorem local_clear_denominator (place : FinitePlace) (value : place.adicCompletion ℚ) :
    ∃ exponent : ℕ, ((Rat.HeightOneSpectrum.primesEquiv place).val : place.adicCompletion ℚ) ^ exponent * value ∈
      place.adicCompletionIntegers ℚ := by
  let _ : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  obtain ⟨exponent, bound⟩ := padic_clear_denominator (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place value)
  refine ⟨exponent, (local_integral_iff_norm place _).mpr ?_⟩
  simpa only [map_mul, map_pow, map_natCast] using bound

theorem integral_iff (value : FiniteAdeles) :
    value ∈ Set.range integralEmbedding ↔ ∀ place : FinitePlace, value place ∈ place.adicCompletionIntegers ℚ := by
  constructor
  · rintro ⟨preimage, rfl⟩ place
    exact (preimage place).property
  · intro membership
    exact ⟨fun place => ⟨value place, membership place⟩, rfl⟩

theorem exists_nat_denominator (value : FiniteAdeles) :
    ∃ denominator : ℕ, denominator ≠ 0 ∧ (denominator : FiniteAdeles) * value ∈ Set.range integralEmbedding := by
  classical
  let badPlaces := {place : FinitePlace | value place ∉ place.adicCompletionIntegers ℚ}
  have finiteBad : badPlaces.Finite := value.property
  let places := finiteBad.toFinset
  choose exponent integral using fun place : FinitePlace => local_clear_denominator place (value place)
  let factor := fun place : FinitePlace => (Rat.HeightOneSpectrum.primesEquiv place).val ^ exponent place
  refine ⟨∏ place ∈ places, factor place, Finset.prod_ne_zero_iff.mpr (fun place _ =>
    pow_ne_zero _ (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero), ?_⟩
  apply (integral_iff _).mpr
  intro place
  by_cases membership : place ∈ places
  · have productEquality : (∏ other ∈ places, factor other) =
        factor place * ∏ other ∈ places.erase place, factor other :=
      (Finset.mul_prod_erase places factor membership).symm
    rw [productEquality]
    change ((factor place * ∏ other ∈ places.erase place, factor other : ℕ) : place.adicCompletion ℚ) * value place ∈ _
    rw [Nat.cast_mul, mul_assoc, mul_comm _ (value place), ← mul_assoc]
    apply (place.adicCompletionIntegers ℚ).mul_mem
    · simpa only [factor, Nat.cast_pow] using integral place
    · exact natCast_mem (place.adicCompletionIntegers ℚ) _
  · have atPlace : value place ∈ place.adicCompletionIntegers ℚ := by
      simpa only [places, Set.Finite.mem_toFinset, badPlaces, Set.mem_ofPred_eq, not_not] using membership
    change ((∏ other ∈ places, factor other : ℕ) : place.adicCompletion ℚ) * value place ∈ _
    exact mul_mem (natCast_mem (place.adicCompletionIntegers ℚ) _) atPlace

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicDenominators
