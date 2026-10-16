module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Schwartz.ThetaContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalAdditiveDomain

scoped instance rationalAction : AddAction ℚ Adeles :=
  AddAction.compHom Adeles rationalAdele.toAddMonoidHom

theorem rational_vadd (rational : ℚ) (value : Adeles) : rational +ᵥ value = rationalAdele rational + value := rfl

scoped instance rationalMeasurable : MeasurableConstVAdd ℚ Adeles :=
  ⟨fun _ => measurable_const.add measurable_id⟩

scoped instance rationalInvariant : VAddInvariantMeasure ℚ Adeles adeleMeasure :=
  ⟨fun rational _ _ => measure_preimage_add adeleMeasure (rationalAdele rational) _⟩

theorem domain_measurable : MeasurableSet additiveDomain :=
  measurableSet_Ico.prod integralLattice_isOpen.measurableSet

theorem exists_representative (value : Adeles) : ∃ rational : ℚ, rational +ᵥ value ∈ additiveDomain := by
  obtain ⟨rational, integral, finiteEquality⟩ := AdelicAdditiveReduction.exists_rational_add_integral value.2
  let integer : ℤ := ⌊value.1 - (rational : ℝ)⌋
  refine ⟨-rational - integer, ?_, ?_⟩
  · change 0 ≤ ((-rational - integer : ℚ) : ℝ) + value.1 ∧
      ((-rational - integer : ℚ) : ℝ) + value.1 < 1
    have lower : (integer : ℝ) ≤ value.1 - (rational : ℝ) := Int.floor_le _
    have upper : value.1 - (rational : ℝ) < (integer : ℝ) + 1 := Int.lt_floor_add_one _
    push_cast
    constructor <;> linarith
  · refine ⟨integral - integer, ?_⟩
    change integralEmbedding (integral - integer) =
      algebraMap ℚ FiniteAdeles (-rational - integer) + value.2
    rw [finiteEquality, map_sub, map_intCast, map_sub, map_neg, map_intCast]
    ring

theorem representative_unique (value : Adeles) (first second : ℚ)
    (firstMembership : first +ᵥ value ∈ additiveDomain) (secondMembership : second +ᵥ value ∈ additiveDomain) :
    first = second := by
  have firstInterval : 0 ≤ (first : ℝ) + value.1 ∧ (first : ℝ) + value.1 < 1 := firstMembership.1
  have secondInterval : 0 ≤ (second : ℝ) + value.1 ∧ (second : ℝ) + value.1 < 1 := secondMembership.1
  have differenceIntegral : algebraMap ℚ FiniteAdeles (first - second) ∈ Set.range integralEmbedding := by
    obtain ⟨firstIntegral, firstEquality⟩ := firstMembership.2
    obtain ⟨secondIntegral, secondEquality⟩ := secondMembership.2
    refine ⟨firstIntegral - secondIntegral, ?_⟩
    change integralEmbedding firstIntegral = algebraMap ℚ FiniteAdeles first + value.2 at firstEquality
    change integralEmbedding secondIntegral = algebraMap ℚ FiniteAdeles second + value.2 at secondEquality
    rw [map_sub, firstEquality, secondEquality, map_sub]
    ring
  obtain ⟨integer, rationalEquality⟩ := (IntegralRationals.integral_iff_integer (first - second)).mp differenceIntegral
  have realEquality : (first : ℝ) - (second : ℝ) = (integer : ℝ) := by exact_mod_cast rationalEquality
  have lower : (-1 : ℝ) < integer := by linarith
  have upper : (integer : ℝ) < 1 := by linarith
  have integerLower : (-1 : ℤ) < integer := by exact_mod_cast lower
  have integerUpper : integer < (1 : ℤ) := by exact_mod_cast upper
  have integerZero : integer = 0 := by omega
  apply sub_eq_zero.mp
  simpa only [integerZero, Int.cast_zero] using rationalEquality

theorem unique_representative (value : Adeles) : ∃! rational : ℚ, rational +ᵥ value ∈ additiveDomain := by
  obtain ⟨rational, membership⟩ := exists_representative value
  exact ⟨rational, membership, fun other otherMembership => representative_unique value other rational otherMembership membership⟩

theorem domain_fundamental : IsAddFundamentalDomain ℚ additiveDomain adeleMeasure :=
  IsAddFundamentalDomain.mk' domain_measurable.nullMeasurableSet unique_representative

scoped instance hasFundamentalDomain : HasAddFundamentalDomain ℚ Adeles adeleMeasure :=
  domain_fundamental.hasAddFundamentalDomain _

theorem integral_unfold {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (function : Adeles → Target) (integrable : Integrable function adeleMeasure) :
    ∫ value, function value ∂adeleMeasure =
      ∑' rational : ℚ, ∫ value in additiveDomain, function (rationalAdele rational + value) ∂adeleMeasure :=
  domain_fundamental.integral_eq_tsum'' function integrable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalAdditiveDomain
