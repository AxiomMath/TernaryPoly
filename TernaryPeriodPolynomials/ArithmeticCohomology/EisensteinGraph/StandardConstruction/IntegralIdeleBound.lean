module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedHeight

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.IntegralIdeleBound

theorem norm_le_one_of_real_one (unit : Adelesˣ) (real : unit.val.1 = 1)
    (integral : unit.val.2 ∈ Set.range integralEmbedding) : adeleNorm unit ≤ 1 := by
  obtain ⟨integer, finiteEquality⟩ := integral
  have inclusion : additiveDomain ⊆ (ContinuousAddEquiv.mulLeft unit) ⁻¹' additiveDomain := by
    rintro ⟨x, y⟩ ⟨realMembership, ⟨finite, finiteMembership⟩⟩
    change (unit.val.1 * x ∈ Set.Ico 0 1) ∧
      unit.val.2 * y ∈ Set.range integralEmbedding
    rw [real, one_mul]
    refine ⟨realMembership, integer * finite, ?_⟩
    rw [map_mul, finiteEquality, finiteMembership]
  have bound := measure_mono (μ := adeleMeasure) inclusion
  rw [Norms.additiveDomain_measure] at bound
  have measureEquality := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := additiveDomain) (ContinuousAddEquiv.mulLeft unit)
  rw [Norms.additiveDomain_measure] at measureEquality
  change (adeleNorm unit : ℝ≥0∞) *
    adeleMeasure ((ContinuousAddEquiv.mulLeft unit) ⁻¹' additiveDomain) = 1 at measureEquality
  have normBound : (adeleNorm unit : ℝ≥0∞) ≤ 1 := by
    calc
      (adeleNorm unit : ℝ≥0∞) = (adeleNorm unit : ℝ≥0∞) * 1 := (mul_one _).symm
      _ ≤ (adeleNorm unit : ℝ≥0∞) *
          adeleMeasure ((ContinuousAddEquiv.mulLeft unit) ⁻¹' additiveDomain) := by gcongr
      _ = 1 := measureEquality
  exact ENNReal.coe_le_coe.mp normBound

theorem norm_le_real (unit : Adelesˣ)
    (integral : unit.val.2 ∈ Set.range integralEmbedding) :
    (adeleNorm unit : ℝ) ≤ |unit.val.1| := by
  let realUnit : ℝˣ := Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom unit
  let remainder := (realAdeleUnit realUnit)⁻¹ * unit
  have realOne : remainder.val.1 = 1 := by
    change realUnit.inv * realUnit.val = 1
    exact realUnit.inv_val
  have finiteIntegral : remainder.val.2 ∈ Set.range integralEmbedding := by
    change (1 : FiniteAdeles) * unit.val.2 ∈ Set.range integralEmbedding
    rwa [one_mul]
  have bound : (adeleNorm remainder : ℝ) ≤ 1 :=
    (NNReal.coe_le_coe).mpr (norm_le_one_of_real_one remainder realOne finiteIntegral)
  have factorization : realAdeleUnit realUnit * remainder = unit := by
    simp [remainder]
  calc
    (adeleNorm unit : ℝ) = |unit.val.1| * (adeleNorm remainder : ℝ) := by
      conv_lhs => rw [← factorization, map_mul, NNReal.coe_mul, Norms.realUnit_norm]
      rfl
    _ ≤ |unit.val.1| := mul_le_of_le_one_right (abs_nonneg _) bound

theorem norm_lower_bound (unit : Adelesˣ) (integer : ℤ) (nonzero : integer ≠ 0)
    (integral : ((integer : Adeles) * unit.inv).2 ∈ Set.range integralEmbedding) :
    |unit.val.1| / |(integer : ℝ)| ≤ (adeleNorm unit : ℝ) := by
  let rational : ℚˣ := Units.mk0 (integer : ℚ) (Int.cast_ne_zero.mpr nonzero)
  let quotient := Units.map rationalAdele.toMonoidHom rational * unit⁻¹
  have quotientIntegral : quotient.val.2 ∈ Set.range integralEmbedding := by
    convert integral using 1
    simp [quotient, rational, Units.val_mul]
  have bound := norm_le_real quotient quotientIntegral
  have normEquality : (adeleNorm quotient : ℝ) = (adeleNorm unit : ℝ)⁻¹ := by
    rw [show quotient = Units.map rationalAdele rational * unit⁻¹ from rfl, map_mul, map_inv]
    rw [RationalNorm.rational_norm rational, one_mul, NNReal.coe_inv]
  have realEquality : |quotient.val.1| = |(integer : ℝ)| / |unit.val.1| := by
    change |((integer : ℚ) : ℝ) * unit.inv.1| = _
    have realInverse : unit.inv.1 = (unit.val.1)⁻¹ := by
      exact Units.val_inv_eq_inv_val (Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom unit)
    rw [Rat.cast_intCast, realInverse, abs_mul, abs_inv, div_eq_mul_inv]
  rw [normEquality, realEquality] at bound
  have realPositive : 0 < |unit.val.1| :=
    abs_pos.mpr (Units.ne_zero (Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom unit))
  have integerPositive : 0 < |(integer : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr nonzero)
  have normPositive : 0 < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  have multiplied := (le_div_iff₀ realPositive).mp bound
  apply (div_le_iff₀ integerPositive).mpr
  have multipliedAgain := mul_le_mul_of_nonneg_left multiplied normPositive.le
  calc
    |unit.val.1| = (adeleNorm unit : ℝ) *
        ((adeleNorm unit : ℝ)⁻¹ * |unit.val.1|) := by rw [← mul_assoc, mul_inv_cancel₀ normPositive.ne', one_mul]
    _ ≤ (adeleNorm unit : ℝ) * |(integer : ℝ)| := multipliedAgain

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.IntegralIdeleBound
