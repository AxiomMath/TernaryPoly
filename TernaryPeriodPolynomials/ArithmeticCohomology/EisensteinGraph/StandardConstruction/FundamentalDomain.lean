module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FiniteApproximation

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FundamentalDomain

instance rationalTranslation : AddAction ℚ Adeles where
  vadd rational value := rationalAdele rational + value
  zero_vadd value := by
    change rationalAdele 0 + value = value
    rw [map_zero, zero_add]
  add_vadd first second value := by
    change rationalAdele (first + second) + value =
      rationalAdele first + (rationalAdele second + value)
    rw [map_add, add_assoc]

theorem translate_exists (value : Adeles) :
    ∃ rational : ℚ, rationalAdele rational + value ∈ additiveDomain := by
  obtain ⟨rational, integral, equality⟩ :=
    FiniteApproximation.rational_translate_integral value.2
  let integer := ⌊value.1 - (rational : ℝ)⌋
  refine ⟨-rational - (integer : ℚ), ?_, ?_⟩
  · change ((-rational - (integer : ℚ) : ℚ) : ℝ) + value.1 ∈ Set.Ico 0 1
    have realEquality : ((-rational - (integer : ℚ) : ℚ) : ℝ) + value.1 =
        Int.fract (value.1 - (rational : ℝ)) := by
      simp only [Rat.cast_sub, Rat.cast_neg, Rat.cast_intCast, Int.fract, integer]
      ring
    rw [realEquality]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  · refine ⟨integral - (integer : IntegralAdeles), ?_⟩
    change integralEmbedding (integral - (integer : IntegralAdeles)) =
      algebraMap ℚ FiniteAdeles (-rational - (integer : ℚ)) + value.2
    rw [map_sub, map_intCast, equality, map_sub, map_neg, map_intCast]
    ring

theorem translate_unique (value : Adeles) (first second : ℚ)
    (firstMembership : rationalAdele first + value ∈ additiveDomain)
    (secondMembership : rationalAdele second + value ∈ additiveDomain) : first = second := by
  obtain ⟨firstReal, firstIntegral, firstEquality⟩ := firstMembership
  obtain ⟨secondReal, secondIntegral, secondEquality⟩ := secondMembership
  have integralDifference : algebraMap ℚ FiniteAdeles (first - second) ∈
      Set.range integralEmbedding := by
    refine ⟨firstIntegral - secondIntegral, ?_⟩
    rw [map_sub, firstEquality, secondEquality, map_sub]
    change (algebraMap ℚ FiniteAdeles first + value.2) -
      (algebraMap ℚ FiniteAdeles second + value.2) = _
    ring
  obtain ⟨integer, integerEquality⟩ :=
    (FiniteApproximation.rational_integral_iff (first - second)).mp integralDifference
  have realEquality : (first : ℝ) - (second : ℝ) = (integer : ℝ) := by
    exact_mod_cast integerEquality
  change 0 ≤ (first : ℝ) + value.1 ∧ (first : ℝ) + value.1 < 1 at firstReal
  change 0 ≤ (second : ℝ) + value.1 ∧ (second : ℝ) + value.1 < 1 at secondReal
  have lower : (-1 : ℤ) < integer := by
    have realLower : (-1 : ℝ) < (integer : ℝ) := by linarith
    exact_mod_cast realLower
  have upper : integer < (1 : ℤ) := by
    have realUpper : (integer : ℝ) < (1 : ℝ) := by linarith
    exact_mod_cast realUpper
  have zero : integer = 0 := by omega
  rw [zero, Int.cast_zero] at integerEquality
  exact sub_eq_zero.mp integerEquality

theorem translate_existsUnique (value : Adeles) :
    ∃! rational : ℚ, rationalAdele rational + value ∈ additiveDomain := by
  obtain ⟨rational, membership⟩ := translate_exists value
  exact ⟨rational, membership, fun other otherMembership =>
    translate_unique value other rational otherMembership membership⟩

theorem additiveDomain_measurable : MeasurableSet additiveDomain :=
  measurableSet_Ico.prod integralLattice_isOpen.measurableSet

theorem additiveDomain_fundamental : IsAddFundamentalDomain ℚ additiveDomain adeleMeasure := by
  apply IsAddFundamentalDomain.mk' additiveDomain_measurable.nullMeasurableSet
  exact translate_existsUnique

instance rationalTranslationMeasurable : MeasurableConstVAdd ℚ Adeles where
  measurable_const_vadd _ := measurable_const.add measurable_id

instance rationalTranslationInvariant : VAddInvariantMeasure ℚ Adeles adeleMeasure where
  measure_preimage_vadd rational _ measurable :=
    (measurePreserving_add_left adeleMeasure (rationalAdele rational)).measure_preimage
      measurable.nullMeasurableSet

def rationalPair (rational : ℚ × ℚ) : Adeles × Adeles :=
  (rationalAdele rational.1, rationalAdele rational.2)

instance rationalPairTranslation : AddAction (ℚ × ℚ) (Adeles × Adeles) where
  vadd rational value := rationalPair rational + value
  zero_vadd value := by
    change rationalPair 0 + value = value
    simp [rationalPair]
  add_vadd first second value := by
    change rationalPair (first + second) + value =
      rationalPair first + (rationalPair second + value)
    have pairAdd : rationalPair (first + second) = rationalPair first + rationalPair second := by
      ext <;> simp [rationalPair]
    rw [pairAdd, add_assoc]

theorem radicalDomain_fundamental : IsAddFundamentalDomain (ℚ × ℚ)
    (additiveDomain ×ˢ additiveDomain) radicalMeasure := by
  apply IsAddFundamentalDomain.mk'
    (additiveDomain_measurable.prod additiveDomain_measurable).nullMeasurableSet
  intro value
  obtain ⟨first, firstMembership, firstUnique⟩ := translate_existsUnique value.1
  obtain ⟨second, secondMembership, secondUnique⟩ := translate_existsUnique value.2
  refine ⟨(first, second), ⟨firstMembership, secondMembership⟩, ?_⟩
  intro other membership
  exact Prod.ext (firstUnique other.1 membership.1) (secondUnique other.2 membership.2)

instance rationalPairTranslationMeasurable :
    MeasurableConstVAdd (ℚ × ℚ) (Adeles × Adeles) where
  measurable_const_vadd _ := measurable_const.add measurable_id

instance rationalPairTranslationInvariant :
    VAddInvariantMeasure (ℚ × ℚ) (Adeles × Adeles) radicalMeasure where
  measure_preimage_vadd rational _ measurable :=
    (measurePreserving_add_left radicalMeasure (rationalPair rational)).measure_preimage
      measurable.nullMeasurableSet

instance additiveDomainProbability : IsProbabilityMeasure (adeleMeasure.restrict additiveDomain) :=
  ⟨by simp [Norms.additiveDomain_measure]⟩

instance radicalDomainProbability :
    IsProbabilityMeasure (radicalMeasure.restrict (additiveDomain ×ˢ additiveDomain)) :=
  ⟨by simp [radicalMeasure, Measure.prod_prod, Norms.additiveDomain_measure]⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FundamentalDomain
