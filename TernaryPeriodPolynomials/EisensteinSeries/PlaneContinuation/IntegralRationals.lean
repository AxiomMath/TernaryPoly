module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Theta.LocalFiniteness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralRationals

theorem eq_zero_of_unit_interval (rational : ℚ)
    (integral : algebraMap ℚ FiniteAdeles rational ∈ Set.range integralEmbedding)
    (nonnegative : 0 ≤ (rational : ℝ)) (small : (rational : ℝ) < 1) : rational = 0 := by
  by_contra nonzero
  let unit : ℚˣ := Units.mk0 rational nonzero
  have measureIdentity := ProductFormula.adeleNorm_eq_measure_image (Units.map rationalAdele.toMonoidHom unit)
  rw [ProductFormula.adeleNorm_rational] at measureIdentity
  have containment : (fun value : Adeles => rationalAdele rational * value) '' additiveDomain ⊆
      Set.Icc 0 (rational : ℝ) ×ˢ Set.range integralEmbedding := by
    rintro _ ⟨value, membership, rfl⟩
    change (0 ≤ value.1 ∧ value.1 < 1) ∧ value.2 ∈ Set.range integralEmbedding at membership
    exact ⟨⟨mul_nonneg nonnegative membership.1.1,
      mul_le_of_le_one_right nonnegative membership.1.2.le⟩,
      RationalDiscreteness.integral_mul integral membership.2⟩
  have measureBound := measure_mono (μ := adeleMeasure) containment
  change 1 = adeleMeasure ((fun value : Adeles => rationalAdele rational * value) '' additiveDomain) at measureIdentity
  rw [← measureIdentity, adeleMeasure, Measure.prod_prod, Real.volume_Icc,
    finiteMeasure_integralLattice, mul_one, sub_zero] at measureBound
  have realBound : 1 ≤ (rational : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff nonnegative).mp (by simpa only [ENNReal.ofReal_one] using measureBound)
  exact (not_le_of_gt small) realBound

theorem integral_iff_integer (rational : ℚ) :
    algebraMap ℚ FiniteAdeles rational ∈ Set.range integralEmbedding ↔ ∃ integer : ℤ, rational = integer := by
  constructor
  · intro integral
    let integer : ℤ := ⌊(rational : ℝ)⌋
    have differenceIntegral : algebraMap ℚ FiniteAdeles (rational - integer) ∈ Set.range integralEmbedding := by
      obtain ⟨value, equality⟩ := integral
      refine ⟨value - integer, ?_⟩
      rw [map_sub, equality, map_intCast, map_sub, map_intCast]
    have differenceNonnegative : 0 ≤ ((rational - integer : ℚ) : ℝ) := by
      push_cast
      exact sub_nonneg.mpr (Int.floor_le (rational : ℝ))
    have differenceSmall : ((rational - integer : ℚ) : ℝ) < 1 := by
      push_cast
      exact (sub_lt_iff_lt_add).mpr (by simpa only [add_comm] using Int.lt_floor_add_one (rational : ℝ))
    exact ⟨integer, sub_eq_zero.mp
      (eq_zero_of_unit_interval (rational - integer) differenceIntegral differenceNonnegative differenceSmall)⟩
  · rintro ⟨integer, rfl⟩
    exact ⟨integer, by rw [map_intCast, map_intCast]⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralRationals
