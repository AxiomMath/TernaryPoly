module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PrimeMeasure
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalNorm

def naturalUnit (number : ℕ) (nonzero : number ≠ 0) : ℚˣ :=
  Units.mk0 (number : ℚ) (Nat.cast_ne_zero.mpr nonzero)

theorem prime_domain_image (prime : ℕ) (isPrime : prime.Prime) :
    (ContinuousAddEquiv.mulLeft
      (Units.map rationalAdele (naturalUnit prime isPrime.ne_zero))) '' additiveDomain =
    Set.Ico (0 : ℝ) prime ×ˢ
      Set.range (fun value : IntegralAdeles =>
        integralEmbedding ((prime : IntegralAdeles) * value)) := by
  have imageInterval := Set.image_mul_left_Ico
    (Nat.cast_pos.mpr isPrime.pos : (0 : ℝ) < prime) 0 1
  simp only [mul_zero, mul_one] at imageInterval
  ext value
  constructor
  · rintro ⟨argument, ⟨realMembership, ⟨integralValue, finiteEquality⟩⟩, equality⟩
    have realEquality : (prime : ℝ) * argument.1 = value.1 := congrArg Prod.fst equality
    have finiteImageEquality : integralEmbedding ((prime : IntegralAdeles) * integralValue) =
        value.2 := by
      rw [map_mul, map_natCast, finiteEquality]
      simpa [ContinuousAddEquiv.mulLeft_apply, naturalUnit, rationalAdele] using
        congrArg Prod.snd equality
    refine ⟨?_, integralValue, finiteImageEquality⟩
    rw [← imageInterval]
    exact ⟨argument.1, realMembership, realEquality⟩
  · rintro ⟨realMembership, ⟨integralValue, finiteEquality⟩⟩
    rw [← imageInterval] at realMembership
    obtain ⟨realValue, intervalMembership, realEquality⟩ := realMembership
    refine ⟨(realValue, integralEmbedding integralValue),
      ⟨intervalMembership, integralValue, rfl⟩, ?_⟩
    apply Prod.ext
    · exact realEquality
    · simp only [ContinuousAddEquiv.mulLeft_apply, Units.coe_map,
        naturalUnit, Units.val_mk0, Prod.snd_mul]
      change algebraMap ℚ FiniteAdeles (prime : ℚ) *
        integralEmbedding integralValue = value.2
      rw [map_natCast, ← map_natCast integralEmbedding, ← map_mul]
      exact finiteEquality

theorem prime_norm (prime : ℕ) (isPrime : prime.Prime) :
    adeleNorm (Units.map rationalAdele (naturalUnit prime isPrime.ne_zero)) = 1 := by
  let equivalence := ContinuousAddEquiv.mulLeft
    (Units.map rationalAdele.toMonoidHom (naturalUnit prime isPrime.ne_zero))
  have measurable : MeasurableEmbedding equivalence :=
    equivalence.toHomeomorph.measurableEmbedding
  have measureEquality := congrArg (fun measure : Measure Adeles => measure additiveDomain)
    (addEquivAddHaarChar_smul_eq_comap adeleMeasure equivalence)
  rw [Measure.smul_apply,
    measurable.comap_apply,
    Norms.additiveDomain_measure] at measureEquality
  change adeleNorm (Units.map rationalAdele (naturalUnit prime isPrime.ne_zero)) •
    (1 : ℝ≥0∞) = adeleMeasure
      ((ContinuousAddEquiv.mulLeft
        (Units.map rationalAdele (naturalUnit prime isPrime.ne_zero))) '' additiveDomain)
    at measureEquality
  rw [prime_domain_image prime isPrime,
    adeleMeasure, Measure.prod_prod, Real.volume_Ico, sub_zero,
    ENNReal.ofReal_natCast, PrimeMeasure.prime_lattice_measure prime isPrime] at measureEquality
  change adeleNorm (Units.map rationalAdele (naturalUnit prime isPrime.ne_zero)) •
    (1 : ℝ≥0∞) = 1 at measureEquality
  simpa only [ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] using measureEquality

theorem natural_norm (number : ℕ) (nonzero : number ≠ 0) :
    adeleNorm (Units.map rationalAdele (naturalUnit number nonzero)) = 1 := by
  have induction : ∀ number : ℕ, ∀ nonzero : number ≠ 0,
      adeleNorm (Units.map rationalAdele (naturalUnit number nonzero)) = 1 := by
    apply Nat.prime_composite_induction
    · intro nonzero
      exact False.elim (nonzero rfl)
    · intro nonzero
      have unitEquality : naturalUnit 1 nonzero = 1 := by
        apply Units.ext
        rfl
      rw [unitEquality, map_one, map_one]
    · intro prime isPrime nonzero
      exact prime_norm prime isPrime
    · intro first firstBound firstInduction second secondBound secondInduction nonzero
      have firstNonzero : first ≠ 0 := by omega
      have secondNonzero : second ≠ 0 := by omega
      have unitEquality : naturalUnit (first * second) nonzero =
          naturalUnit first firstNonzero * naturalUnit second secondNonzero := by
        apply Units.ext
        exact Nat.cast_mul first second
      rw [unitEquality, map_mul, map_mul, firstInduction firstNonzero,
        secondInduction secondNonzero, one_mul]
  exact induction number nonzero

theorem integer_norm (number : ℤ) (nonzero : number ≠ 0) :
    adeleNorm (Units.map rationalAdele
      (Units.mk0 (number : ℚ) (Int.cast_ne_zero.mpr nonzero))) = 1 := by
  have absoluteNonzero : number.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr nonzero
  rcases le_total 0 number with nonnegative | nonpositive
  · have unitEquality : Units.mk0 (number : ℚ) (Int.cast_ne_zero.mpr nonzero) =
        naturalUnit number.natAbs absoluteNonzero := by
      apply Units.ext
      change (number : ℚ) = (number.natAbs : ℚ)
      simpa only [Int.cast_natCast] using
        congrArg (Int.cast : ℤ → ℚ) (Int.eq_natAbs_of_nonneg nonnegative)
    rw [unitEquality]
    exact natural_norm number.natAbs absoluteNonzero
  · have unitEquality : Units.mk0 (number : ℚ) (Int.cast_ne_zero.mpr nonzero) =
        (-1 : ℚˣ) * naturalUnit number.natAbs absoluteNonzero := by
      apply Units.ext
      change (number : ℚ) = -1 * (number.natAbs : ℚ)
      rw [neg_one_mul]
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (Int.cast : ℤ → ℚ) (Int.eq_neg_natAbs_of_nonpos nonpositive)
    rw [unitEquality, map_mul, map_mul, Norms.rational_negative_one_norm,
      natural_norm number.natAbs absoluteNonzero, one_mul]

theorem rational_norm (rationalUnit : ℚˣ) :
    adeleNorm (Units.map rationalAdele rationalUnit) = 1 := by
  have numeratorNonzero : rationalUnit.val.num ≠ 0 :=
    Rat.num_ne_zero.mpr rationalUnit.ne_zero
  let numerator : ℚˣ := Units.mk0 (rationalUnit.val.num : ℚ)
    (Int.cast_ne_zero.mpr numeratorNonzero)
  let denominator : ℚˣ := naturalUnit rationalUnit.val.den (Rat.den_nz rationalUnit.val)
  have unitEquality : rationalUnit = numerator * denominator⁻¹ := by
    apply Units.ext
    change rationalUnit.val = (rationalUnit.val.num : ℚ) *
      (rationalUnit.val.den : ℚ)⁻¹
    rw [← div_eq_mul_inv]
    exact (Rat.num_div_den rationalUnit.val).symm
  rw [unitEquality, map_mul, map_mul, map_inv, map_inv,
    integer_norm rationalUnit.val.num numeratorNonzero,
    natural_norm rationalUnit.val.den (Rat.den_nz rationalUnit.val), inv_one, one_mul]

theorem sourceComparison {degree : ℕ} (data : InducingData degree) :
    SourceComparisonExists data := by
  exact RationalComparison.sourceComparison_of_rationalNorm data rational_norm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalNorm
