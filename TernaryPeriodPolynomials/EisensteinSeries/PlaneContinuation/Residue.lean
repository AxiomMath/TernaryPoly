module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Residue

noncomputable def reduction (place : FinitePlace) :
    IntegralAdeles →+* ZMod (Rat.HeightOneSpectrum.primesEquiv place).val := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  let : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact PadicInt.toZMod.comp
    ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place).toRingHom.comp
      (Pi.evalRingHom (fun v : FinitePlace => v.adicCompletionIntegers ℚ) place))

theorem local_natCast_isUnit (place : FinitePlace) (prime : Nat.Primes)
    (different : Rat.HeightOneSpectrum.primesEquiv place ≠ prime) :
    IsUnit (prime.val : place.adicCompletionIntegers ℚ) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  let : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let equivalence := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place
  have coprimality : (Rat.HeightOneSpectrum.primesEquiv place).val.Coprime prime.val := by
    apply (Rat.HeightOneSpectrum.primesEquiv place).property.coprime_iff_not_dvd.mpr
    intro divides
    have equalPrimes : (Rat.HeightOneSpectrum.primesEquiv place).val = prime.val :=
      (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.primesEquiv place).property
        prime.property).mp divides
    exact different (Subtype.ext equalPrimes)
  have unitImage : IsUnit
      (prime.val : ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr coprimality)
  simpa using unitImage.map equivalence.symm.toRingHom

theorem reduction_eq_zero_iff (place : FinitePlace) (value : IntegralAdeles) :
    reduction place value = 0 ↔
      ((Rat.HeightOneSpectrum.primesEquiv place).val : IntegralAdeles) ∣ value := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  let : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  constructor
  · intro zeroReduction
    let equivalence := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place
    have localDivisibility :
        ((Rat.HeightOneSpectrum.primesEquiv place).val :
          ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) ∣ equivalence (value place) := by
      apply Ideal.mem_span_singleton.mp
      rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
      exact zeroReduction
    have atPlace : ((Rat.HeightOneSpectrum.primesEquiv place).val :
        place.adicCompletionIntegers ℚ) ∣ value place := by
      rcases localDivisibility with ⟨quotient, quotientProperty⟩
      refine ⟨equivalence.symm quotient, ?_⟩
      simpa using congrArg equivalence.symm quotientProperty
    have atEveryPlace (other : FinitePlace) :
        ((Rat.HeightOneSpectrum.primesEquiv place).val :
          other.adicCompletionIntegers ℚ) ∣ value other := by
      by_cases equalPlaces : other = place
      · subst other
        exact atPlace
      · exact (local_natCast_isUnit other (Rat.HeightOneSpectrum.primesEquiv place)
          (fun equalPrimes => equalPlaces
            (Rat.HeightOneSpectrum.primesEquiv.injective equalPrimes))).dvd
    choose quotient quotientProperty using atEveryPlace
    exact ⟨quotient, funext quotientProperty⟩
  · rintro ⟨quotient, rfl⟩
    simp

theorem exists_residue_quotient (place : FinitePlace) (value : IntegralAdeles) :
    ∃ quotient : IntegralAdeles,
      (reduction place value).val +
        ((Rat.HeightOneSpectrum.primesEquiv place).val : IntegralAdeles) * quotient = value := by
  let : NeZero (Rat.HeightOneSpectrum.primesEquiv place).val :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero⟩
  have zeroReduction : reduction place (value - (reduction place value).val) = 0 := by
    simp
  obtain ⟨quotient, quotientProperty⟩ :=
    (reduction_eq_zero_iff place _).mp zeroReduction
  refine ⟨quotient, ?_⟩
  rw [← quotientProperty]
  abel

noncomputable def finiteResidueCoset (place : FinitePlace)
    (residue : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val) : Set FiniteAdeles :=
  Set.range (fun value : IntegralAdeles => (residue.val : FiniteAdeles) +
    ((Rat.HeightOneSpectrum.primesEquiv place).val : FiniteAdeles) * integralEmbedding value)

theorem finiteResidueCoset_mem (place : FinitePlace)
    (residue : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val) (value : IntegralAdeles) :
    integralEmbedding value ∈ finiteResidueCoset place residue ↔ reduction place value = residue := by
  let : NeZero (Rat.HeightOneSpectrum.primesEquiv place).val :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero⟩
  constructor
  · rintro ⟨quotient, quotientProperty⟩
    have integralEquality : (residue.val : IntegralAdeles) +
        ((Rat.HeightOneSpectrum.primesEquiv place).val : IntegralAdeles) * quotient = value := by
      apply integralEmbedding_injective
      simpa only [map_add, map_mul, map_natCast] using quotientProperty
    have residueEquality := congrArg (reduction place) integralEquality
    simpa using residueEquality.symm
  · intro residueEquality
    obtain ⟨quotient, quotientProperty⟩ := exists_residue_quotient place value
    refine ⟨quotient, ?_⟩
    rw [residueEquality] at quotientProperty
    simpa only [map_add, map_mul, map_natCast] using
      congrArg integralEmbedding quotientProperty

theorem finiteResidueCoset_subset (place : FinitePlace)
    (residue : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val) :
    finiteResidueCoset place residue ⊆ Set.range integralEmbedding := by
  rintro _ ⟨value, rfl⟩
  exact ⟨(residue.val : IntegralAdeles) +
    ((Rat.HeightOneSpectrum.primesEquiv place).val : IntegralAdeles) * value, by simp⟩

theorem finiteResidueCosets_cover (place : FinitePlace) :
    (⋃ residue, finiteResidueCoset place residue) = Set.range integralEmbedding := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (finiteResidueCoset_subset place)
  · rintro _ ⟨value, rfl⟩
    exact Set.mem_iUnion.mpr ⟨reduction place value,
      (finiteResidueCoset_mem place _ value).mpr rfl⟩

theorem finiteResidueCosets_disjoint (place : FinitePlace) :
    Pairwise (Function.onFun Disjoint (finiteResidueCoset place)) := by
  intro first second different
  apply Set.disjoint_left.mpr
  intro value firstMembership secondMembership
  obtain ⟨integerValue, rfl⟩ := finiteResidueCoset_subset place first firstMembership
  apply different
  exact ((finiteResidueCoset_mem place first integerValue).mp firstMembership).symm.trans
    ((finiteResidueCoset_mem place second integerValue).mp secondMembership)

theorem finiteResidueCoset_compact (place : FinitePlace)
    (residue : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val) :
    IsCompact (finiteResidueCoset place residue) :=
  isCompact_range (continuous_const.add
    (continuous_const.mul integralEmbedding_isOpenEmbedding.continuous))

theorem finiteResidueCoset_measure (place : FinitePlace)
    (residue : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val) :
    finiteMeasure (finiteResidueCoset place residue) =
      finiteMeasure (finiteResidueCoset place 0) := by
  have translatePreimage :
      (fun value : FiniteAdeles => (residue.val : FiniteAdeles) + value) ⁻¹'
        finiteResidueCoset place residue = finiteResidueCoset place 0 := by
    ext value
    change (∃ quotient : IntegralAdeles, (residue.val : FiniteAdeles) +
        ((Rat.HeightOneSpectrum.primesEquiv place).val : FiniteAdeles) *
          integralEmbedding quotient = (residue.val : FiniteAdeles) + value) ↔
      ∃ quotient : IntegralAdeles, ((0 : ZMod
        (Rat.HeightOneSpectrum.primesEquiv place).val).val : FiniteAdeles) +
        ((Rat.HeightOneSpectrum.primesEquiv place).val : FiniteAdeles) *
          integralEmbedding quotient = value
    simp
  rw [← translatePreimage, measure_preimage_add]

theorem finiteMeasure_primeSublattice (place : FinitePlace) :
    ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ≥0∞) *
      finiteMeasure (finiteResidueCoset place 0) = 1 := by
  let : NeZero (Rat.HeightOneSpectrum.primesEquiv place).val :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero⟩
  have measureUnion := measure_iUnion (μ := finiteMeasure)
    (finiteResidueCosets_disjoint place)
    (fun residue => (finiteResidueCoset_compact place residue).measurableSet)
  rw [finiteResidueCosets_cover, finiteMeasure_integralLattice] at measureUnion
  simpa [finiteResidueCoset_measure, tsum_fintype] using measureUnion.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Residue
