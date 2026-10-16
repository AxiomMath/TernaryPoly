module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Residue
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped NNReal ENNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula

theorem adeleNorm_eq_measure_image (unit : Adelesˣ) :
    (adeleNorm unit : ℝ≥0∞) =
      adeleMeasure ((fun value : Adeles => unit.val * value) '' additiveDomain) := by
  have measureIdentity := addEquivAddHaarChar_smul_preimage adeleMeasure
    (ContinuousAddEquiv.mulLeft unit)
    (X := (ContinuousAddEquiv.mulLeft unit) '' additiveDomain)
  rw [Set.preimage_image_eq _ (ContinuousAddEquiv.mulLeft unit).injective,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleMeasure_additiveDomain] at measureIdentity
  exact (mul_one _).symm.trans measureIdentity

theorem natCast_image_domain (integer : ℕ) (positive : 0 < integer) :
    (fun value : Adeles => (integer : Adeles) * value) '' additiveDomain =
      Set.Ico 0 (integer : ℝ) ×ˢ
        Set.range (fun value : IntegralAdeles =>
          (integer : FiniteAdeles) * integralEmbedding value) := by
  change (fun value : ℝ × FiniteAdeles =>
      ((integer : ℝ) * value.1, (integer : FiniteAdeles) * value.2)) ''
        (Set.Ico 0 1 ×ˢ Set.range integralEmbedding) = _
  rw [← Set.prod_image_image_eq,
    Set.image_mul_left_Ico (by exact_mod_cast positive : 0 < (integer : ℝ)),
    mul_zero, mul_one, ← Set.range_comp]
  rfl

theorem adeleMeasure_natCast_image (integer : ℕ) (positive : 0 < integer) :
    adeleMeasure ((fun value : Adeles => (integer : Adeles) * value) '' additiveDomain) =
      (integer : ℝ≥0∞) * finiteMeasure (Set.range (fun value : IntegralAdeles =>
        (integer : FiniteAdeles) * integralEmbedding value)) := by
  rw [natCast_image_domain integer positive, adeleMeasure, Measure.prod_prod,
    Real.volume_Ico, sub_zero, ENNReal.ofReal_natCast]

theorem adeleNorm_rational_prime (prime : Nat.Primes) :
    adeleNorm (Units.map rationalAdele.toMonoidHom
      (Units.mk0 (prime.val : ℚ) (by exact_mod_cast prime.property.ne_zero))) = 1 := by
  have residueMeasure := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Residue.finiteMeasure_primeSublattice
    (Rat.HeightOneSpectrum.primesEquiv.symm prime)
  simp only [Equiv.apply_symm_apply, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Residue.finiteResidueCoset,
    ZMod.val_zero, Nat.cast_zero, zero_add] at residueMeasure
  apply ENNReal.coe_injective
  rw [adeleNorm_eq_measure_image]
  change adeleMeasure ((fun value : Adeles => rationalAdele (prime.val : ℚ) * value) ''
    additiveDomain) = 1
  rw [map_natCast, adeleMeasure_natCast_image prime.val prime.property.pos]
  exact residueMeasure

noncomputable def rationalNorm : ℚˣ →* ℝ≥0 :=
  adeleNorm.comp (Units.map rationalAdele.toMonoidHom)

theorem rationalNorm_prime (prime : Nat.Primes) :
    rationalNorm (Units.mk0 (prime.val : ℚ) (by exact_mod_cast prime.property.ne_zero)) = 1 :=
  adeleNorm_rational_prime prime

theorem rationalNorm_natCast (integer : ℕ) (nonzero : integer ≠ 0) :
    rationalNorm (Units.mk0 (integer : ℚ) (by exact_mod_cast nonzero)) = 1 := by
  induction integer using Nat.recOnMul with
  | zero => exact (nonzero rfl).elim
  | one => simp
  | prime prime primeProperty => exact rationalNorm_prime ⟨prime, primeProperty⟩
  | mul first second firstHypothesis secondHypothesis =>
    have firstNonzero : first ≠ 0 := (mul_ne_zero_iff.mp nonzero).1
    have secondNonzero : second ≠ 0 := (mul_ne_zero_iff.mp nonzero).2
    have unitProduct : Units.mk0 ((first * second : ℕ) : ℚ)
        (by exact_mod_cast nonzero) =
        Units.mk0 (first : ℚ) (by exact_mod_cast firstNonzero) *
          Units.mk0 (second : ℚ) (by exact_mod_cast secondNonzero) := by
      apply Units.ext
      simp
    rw [unitProduct, map_mul, firstHypothesis firstNonzero, secondHypothesis secondNonzero,
      one_mul]

theorem rationalNorm_neg_one : rationalNorm (-1) = 1 := by
  have unitSquare : (-1 : ℚˣ) * (-1) = 1 := by simp
  have normSquare := congrArg (fun unit => (rationalNorm unit : ℝ)) unitSquare
  simp only [map_mul, NNReal.coe_mul, map_one, NNReal.coe_one] at normSquare
  apply NNReal.coe_injective
  change (rationalNorm (-1) : ℝ) = 1
  nlinarith [NNReal.coe_nonneg (rationalNorm (-1))]

theorem rationalNorm_intCast (integer : ℤ) (nonzero : integer ≠ 0) :
    rationalNorm (Units.mk0 (integer : ℚ) (by exact_mod_cast nonzero)) = 1 := by
  rcases le_total 0 integer with nonnegative | nonpositive
  · have integerValue : ((integer.natAbs : ℕ) : ℤ) = integer :=
      (Int.natCast_natAbs integer).trans (abs_of_nonneg nonnegative)
    have unitValue : Units.mk0 (integer : ℚ) (by exact_mod_cast nonzero) =
        Units.mk0 (integer.natAbs : ℚ)
          (by exact_mod_cast Int.natAbs_ne_zero.mpr nonzero) := by
      apply Units.ext
      change (integer : ℚ) = (integer.natAbs : ℚ)
      simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℚ) integerValue.symm
    rw [unitValue]
    exact rationalNorm_natCast _ (Int.natAbs_ne_zero.mpr nonzero)
  · have integerValue : ((integer.natAbs : ℕ) : ℤ) = -integer :=
      (Int.natCast_natAbs integer).trans (abs_of_nonpos nonpositive)
    have unitValue : Units.mk0 (integer : ℚ) (by exact_mod_cast nonzero) =
        (-1 : ℚˣ) * Units.mk0 (integer.natAbs : ℚ)
          (by exact_mod_cast Int.natAbs_ne_zero.mpr nonzero) := by
      apply Units.ext
      change (integer : ℚ) = -1 * (integer.natAbs : ℚ)
      have castEquality : (integer.natAbs : ℚ) = -(integer : ℚ) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using
          congrArg (Int.cast : ℤ → ℚ) integerValue
      rw [castEquality]
      ring
    rw [unitValue, map_mul, rationalNorm_neg_one,
      rationalNorm_natCast _ (Int.natAbs_ne_zero.mpr nonzero), one_mul]

theorem rationalNorm_eq_one (unit : ℚˣ) : rationalNorm unit = 1 := by
  have numeratorNonzero : unit.val.num ≠ 0 := Rat.num_ne_zero.mpr unit.ne_zero
  let numerator : ℚˣ := Units.mk0 (unit.val.num : ℚ) (by exact_mod_cast numeratorNonzero)
  let denominator : ℚˣ := Units.mk0 (unit.val.den : ℚ)
    (by exact_mod_cast unit.val.den_ne_zero)
  have numeratorProduct : numerator = unit * denominator := by
    apply Units.ext
    exact (Rat.mul_den_eq_num unit.val).symm
  have normProduct := congrArg rationalNorm numeratorProduct
  rw [map_mul] at normProduct
  have numeratorNorm : rationalNorm numerator = 1 :=
    rationalNorm_intCast unit.val.num numeratorNonzero
  have denominatorNorm : rationalNorm denominator = 1 :=
    rationalNorm_natCast unit.val.den unit.val.den_ne_zero
  rw [numeratorNorm, denominatorNorm, mul_one] at normProduct
  exact normProduct.symm

theorem adeleNorm_rational (unit : ℚˣ) :
    adeleNorm (Units.map rationalAdele.toMonoidHom unit) = 1 := rationalNorm_eq_one unit

theorem normPower_rational (unit : ℚˣ) (exponent : ℂ) :
    normPower (Units.map rationalAdele.toMonoidHom unit) exponent = 1 := by
  unfold normPower
  rw [adeleNorm_rational]
  simp

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula
