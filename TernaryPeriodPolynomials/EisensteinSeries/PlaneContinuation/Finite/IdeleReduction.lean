module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.AdditiveReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteIdeleReduction

local instance placePrime (place : FinitePlace) : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩

noncomputable def localUnit (place : FinitePlace) : FiniteAdelesˣ →* ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]ˣ :=
  (Units.map (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place).toMonoidHom).comp
    (Units.map (finiteEvaluation place).toMonoidHom)

noncomputable def localNorm (place : FinitePlace) : FiniteAdelesˣ →* ℝ where
  toFun value := ‖(localUnit place value).val‖
  map_one' := by simp
  map_mul' first second := by simp

theorem localNorm_pos (place : FinitePlace) (value : FiniteAdelesˣ) : 0 < localNorm place value :=
  norm_pos_iff.mpr (localUnit place value).ne_zero

theorem localNorm_integral (place : FinitePlace) (value : FiniteAdelesˣ)
    (membership : value.val place ∈ place.adicCompletionIntegers ℚ) : localNorm place value ≤ 1 :=
  (AdelicDenominators.local_integral_iff_norm place _).mp membership

theorem localNorm_one_of_integral (place : FinitePlace) (value : FiniteAdelesˣ)
    (membership : value.val place ∈ place.adicCompletionIntegers ℚ)
    (inverseMembership : value.inv place ∈ place.adicCompletionIntegers ℚ) : localNorm place value = 1 := by
  have bound := localNorm_integral place value membership
  have inverseBound := localNorm_integral place value⁻¹ inverseMembership
  have product : localNorm place value * localNorm place value⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  nlinarith [localNorm_pos place value]

theorem finite_nonunit_places (value : FiniteAdelesˣ) : {place : FinitePlace | localNorm place value ≠ 1}.Finite := by
  have eventual := value.val.property.and value.inv.property
  apply Filter.Eventually.mono eventual
  intro place membership
  exact localNorm_one_of_integral place value membership.1 membership.2

noncomputable def rationalUnit : ℚˣ →* FiniteAdelesˣ := Units.map (algebraMap ℚ FiniteAdeles).toMonoidHom

theorem localUnit_rational (place : FinitePlace) (value : ℚˣ) :
    (localUnit place (rationalUnit value)).val = (value.val : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) := by
  change Rat.HeightOneSpectrum.adicCompletion.padicEquiv place
    (finiteEvaluation place (algebraMap ℚ FiniteAdeles value.val)) = _
  rw [finiteEvaluation_rational]
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place).commutes value.val

noncomputable def primeUnit (prime : Nat.Primes) : ℚˣ :=
  Units.mk0 (prime.val : ℚ) (by exact_mod_cast prime.property.ne_zero)

theorem localNorm_prime (place : FinitePlace) :
    localNorm place (rationalUnit (primeUnit (Rat.HeightOneSpectrum.primesEquiv place))) =
      ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ)⁻¹ := by
  change ‖(localUnit place (rationalUnit _)).val‖ = _
  rw [localUnit_rational]
  simpa only [primeUnit, Units.val_mk0, Rat.cast_natCast] using
    (Padic.norm_p (p := (Rat.HeightOneSpectrum.primesEquiv place).val))

theorem localNorm_other_prime (place : FinitePlace) (prime : Nat.Primes)
    (different : Rat.HeightOneSpectrum.primesEquiv place ≠ prime) :
    localNorm place (rationalUnit (primeUnit prime)) = 1 := by
  change ‖(localUnit place (rationalUnit _)).val‖ = _
  rw [localUnit_rational]
  change ‖(prime.val : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])‖ = 1
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply (Rat.HeightOneSpectrum.primesEquiv place).property.coprime_iff_not_dvd.mpr
  intro divides
  apply different
  exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq
    (Rat.HeightOneSpectrum.primesEquiv place).property prime.property).mp divides)

theorem localNorm_valuation (place : FinitePlace) (value : FiniteAdelesˣ) :
    localNorm place value = ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ) ^
      (-(localUnit place value).val.valuation) :=
  Padic.norm_eq_zpow_neg_valuation (localUnit place value).ne_zero

theorem localNorm_zpow (place : FinitePlace) (value : FiniteAdelesˣ) (exponent : ℤ) :
    localNorm place (value ^ exponent) = localNorm place value ^ exponent := by
  change ‖(localUnit place (value ^ exponent)).val‖ = ‖(localUnit place value).val‖ ^ exponent
  rw [map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow]

theorem exists_rational_matching_norms (value : FiniteAdelesˣ) :
    ∃ rational : ℚˣ, ∀ place : FinitePlace, localNorm place (rationalUnit rational) = localNorm place value := by
  classical
  let places := (finite_nonunit_places value).toFinset
  let exponent := fun place : FinitePlace => (localUnit place value).val.valuation
  refine ⟨∏ place ∈ places, primeUnit (Rat.HeightOneSpectrum.primesEquiv place) ^ exponent place, ?_⟩
  intro place
  simp only [map_prod, map_zpow]
  by_cases membership : place ∈ places
  · rw [Finset.prod_eq_single_of_mem place membership]
    · rw [localNorm_prime, inv_zpow, ← zpow_neg]
      exact (localNorm_valuation place value).symm
    · intro other _ different
      rw [localNorm_other_prime place _ (fun equality =>
        different (Rat.HeightOneSpectrum.primesEquiv.injective equality.symm)), one_zpow]
  · have localEquality : localNorm place value = 1 := by
      simpa only [places, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using membership
    rw [localEquality]
    apply Finset.prod_eq_one
    intro other otherMembership
    rw [localNorm_other_prime place _ (fun equality => membership
      (Rat.HeightOneSpectrum.primesEquiv.injective equality ▸ otherMembership)), one_zpow]

theorem exists_integralUnit_of_norms_one (value : FiniteAdelesˣ)
    (norms : ∀ place : FinitePlace, localNorm place value = 1) :
    ∃ integral : IntegralAdelesˣ, Units.map integralEmbedding.toMonoidHom integral = value := by
  have membership (place : FinitePlace) : value.val place ∈ place.adicCompletionIntegers ℚ :=
    (AdelicDenominators.local_integral_iff_norm place _).mpr (le_of_eq (norms place))
  have inverseNorm (place : FinitePlace) : localNorm place value⁻¹ = 1 := by
    have product : localNorm place value * localNorm place value⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    simpa only [norms, one_mul] using product
  have inverseMembership (place : FinitePlace) : value.inv place ∈ place.adicCompletionIntegers ℚ :=
    (AdelicDenominators.local_integral_iff_norm place _).mpr (le_of_eq (inverseNorm place))
  let integral : IntegralAdelesˣ :=
    ⟨(fun place => ⟨value.val place, membership place⟩),
      (fun place => ⟨value.inv place, inverseMembership place⟩), by
        funext place
        apply Subtype.ext
        exact congrArg (finiteEvaluation place) value.val_inv, by
        funext place
        apply Subtype.ext
        exact congrArg (finiteEvaluation place) value.inv_val⟩
  exact ⟨integral, Units.ext rfl⟩

theorem exists_rational_mul_integral (value : FiniteAdelesˣ) :
    ∃ rational : ℚˣ, ∃ integral : IntegralAdelesˣ,
      value = rationalUnit rational * Units.map integralEmbedding.toMonoidHom integral := by
  obtain ⟨rational, matching⟩ := exists_rational_matching_norms value
  have norms (place : FinitePlace) : localNorm place ((rationalUnit rational)⁻¹ * value) = 1 := by
    have product : localNorm place (rationalUnit rational)⁻¹ * localNorm place (rationalUnit rational) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rwa [map_mul, ← matching]
  obtain ⟨integral, equality⟩ := exists_integralUnit_of_norms_one _ norms
  refine ⟨rational, integral, ?_⟩
  rw [equality, mul_inv_cancel_left]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteIdeleReduction
