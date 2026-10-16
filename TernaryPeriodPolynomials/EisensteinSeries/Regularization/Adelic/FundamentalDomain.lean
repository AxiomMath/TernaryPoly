module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.Approximation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem rational_translate_mem_additiveDomain (value : Adeles) :
    ∃ rational : ℚ, value - rationalAdele rational ∈ additiveDomain := by
  obtain ⟨rational, integralValue, approximation⟩ := finiteAdele_rational_approximation value.2
  let integer := Int.floor (value.1 - (rational : ℝ))
  refine ⟨rational + integer, ?_, ?_⟩
  · change value.1 - ((rational + integer : ℚ) : ℝ) ∈ Set.Ico 0 1
    simp only [Rat.cast_add, Rat.cast_intCast, Set.mem_Ico]
    have lower := Int.floor_le (value.1 - (rational : ℝ))
    have upper := Int.lt_floor_add_one (value.1 - (rational : ℝ))
    dsimp [integer]
    constructor <;> linarith
  · refine ⟨integralValue - (integer : IntegralAdeles), ?_⟩
    change integralEmbedding (integralValue - (integer : IntegralAdeles)) =
      value.2 - algebraMap ℚ FiniteAdeles (rational + integer)
    rw [map_sub, map_intCast, map_add, map_intCast, ← approximation]
    ring

theorem rational_abs_ge_one_of_finite_integral (rational : ℚ) (nonzero : rational ≠ 0)
    (finite_integral : algebraMap ℚ FiniteAdeles rational ∈ Set.range integralEmbedding) :
    1 ≤ |(rational : ℝ)| := by
  have real_nonzero : (rational : ℝ) ≠ 0 := by exact_mod_cast nonzero
  have finite_image_subset :
      (fun value : FiniteAdeles => algebraMap ℚ FiniteAdeles rational * value) ''
        Set.range integralEmbedding ⊆ Set.range integralEmbedding := by
    obtain ⟨integralScalar, scalar_spec⟩ := finite_integral
    rintro _ ⟨_, ⟨integralValue, rfl⟩, rfl⟩
    refine ⟨integralScalar * integralValue, ?_⟩
    rw [map_mul, scalar_spec]
  have real_image : (fun value : ℝ => (rational : ℝ) * value) '' Set.Ico 0 1 =
      (fun value : ℝ => (rational : ℝ)⁻¹ * value) ⁻¹' Set.Ico 0 1 := by
    ext value
    constructor
    · rintro ⟨preimage, preimage_mem, rfl⟩
      simpa only [Set.mem_preimage, ← mul_assoc, inv_mul_cancel₀ real_nonzero, one_mul]
        using preimage_mem
    · intro value_mem
      exact ⟨(rational : ℝ)⁻¹ * value, value_mem, by
        dsimp only
        rw [← mul_assoc, mul_inv_cancel₀ real_nonzero, one_mul]⟩
  have real_measure : volume ((fun value : ℝ => (rational : ℝ) * value) '' Set.Ico 0 1) =
      ENNReal.ofReal |(rational : ℝ)| := by
    rw [real_image, Real.volume_preimage_mul_left (inv_ne_zero real_nonzero), inv_inv,
      Real.volume_Ico]
    norm_num
  have image_equal :
      (fun value : Adeles => (Units.map rationalAdele (Units.mk0 rational nonzero)).val * value) ''
        additiveDomain =
      ((fun value : ℝ => (rational : ℝ) * value) '' Set.Ico 0 1) ×ˢ
        ((fun value : FiniteAdeles => algebraMap ℚ FiniteAdeles rational * value) ''
          Set.range integralEmbedding) := by
    change Prod.map (fun value : ℝ => (rational : ℝ) * value)
      (fun value : FiniteAdeles => algebraMap ℚ FiniteAdeles rational * value) ''
      (Set.Ico 0 1 ×ˢ Set.range integralEmbedding) = _
    rw [Set.prodMap_image_prod]
  have image_measure := adeleNorm_mul_image
    (Units.map rationalAdele (Units.mk0 rational nonzero)) additiveDomain
  rw [adeleNorm_rational, adeleMeasure_additiveDomain, image_equal, adeleMeasure,
    Measure.prod_prod, real_measure] at image_measure
  have finite_measure_bound := measure_mono (μ := finiteMeasure) finite_image_subset
  rw [finiteMeasure_integralLattice] at finite_measure_bound
  apply ENNReal.one_le_ofReal.mp
  calc
    (1 : ENNReal) = ENNReal.ofReal |(rational : ℝ)| *
        finiteMeasure ((fun value : FiniteAdeles => algebraMap ℚ FiniteAdeles rational * value) ''
          Set.range integralEmbedding) := by simpa only [ENNReal.coe_one, one_mul] using image_measure
    _ ≤ ENNReal.ofReal |(rational : ℝ)| * 1 := by
      gcongr
    _ = _ := mul_one _

theorem rational_translate_unique (value : Adeles) {first second : ℚ}
    (first_spec : value - rationalAdele first ∈ additiveDomain)
    (second_spec : value - rationalAdele second ∈ additiveDomain) : first = second := by
  by_contra different
  obtain ⟨first_integral, first_finite⟩ := first_spec.2
  obtain ⟨second_integral, second_finite⟩ := second_spec.2
  change integralEmbedding first_integral = value.2 - algebraMap ℚ FiniteAdeles first at first_finite
  change integralEmbedding second_integral = value.2 - algebraMap ℚ FiniteAdeles second at second_finite
  have finite_difference : algebraMap ℚ FiniteAdeles (first - second) ∈ Set.range integralEmbedding := by
    refine ⟨second_integral - first_integral, ?_⟩
    rw [map_sub, second_finite, first_finite, map_sub]
    ring
  have norm_lower := rational_abs_ge_one_of_finite_integral (first - second)
    (sub_ne_zero.mpr different) finite_difference
  have first_real := first_spec.1
  have second_real := second_spec.1
  change 0 ≤ value.1 - (first : ℝ) ∧ value.1 - (first : ℝ) < 1 at first_real
  change 0 ≤ value.1 - (second : ℝ) ∧ value.1 - (second : ℝ) < 1 at second_real
  have norm_upper : |((first - second : ℚ) : ℝ)| < 1 := by
    rw [Rat.cast_sub, abs_lt]
    constructor <;> linarith [first_real.1, first_real.2, second_real.1, second_real.2]
  exact (not_lt_of_ge norm_lower) norm_upper

noncomputable def rationalLattice : AddSubgroup Adeles := rationalAdele.toAddMonoidHom.range

theorem additiveDomain_isFundamental :
    IsAddFundamentalDomain rationalLattice additiveDomain adeleMeasure := by
  apply IsAddFundamentalDomain.mk'
  · exact (measurableSet_Ico.prod integralLattice_isCompact.measurableSet).nullMeasurableSet
  · intro value
    obtain ⟨rational, rational_spec⟩ := rational_translate_mem_additiveDomain value
    refine ⟨⟨rationalAdele (-rational), ⟨-rational, rfl⟩⟩, ?_, ?_⟩
    · change rationalAdele (-rational) + value ∈ additiveDomain
      simpa only [map_neg, sub_eq_add_neg, add_comm] using rational_spec
    · intro other other_spec
      obtain ⟨other_rational, other_value⟩ := other.property
      have other_translate : value - rationalAdele (-other_rational) ∈ additiveDomain := by
        change other.val + value ∈ additiveDomain at other_spec
        rw [← other_value] at other_spec
        change rationalAdele other_rational + value ∈ additiveDomain at other_spec
        simpa only [map_neg, sub_neg_eq_add, add_comm] using other_spec
      have equal_rational := rational_translate_unique value other_translate rational_spec
      apply Subtype.ext
      change other.val = rationalAdele (-rational)
      rw [← equal_rational, neg_neg]
      exact other_value.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
