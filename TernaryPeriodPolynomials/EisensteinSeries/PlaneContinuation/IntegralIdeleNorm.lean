module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RecoveryMellin

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeMeasure
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralIdeleNorm

theorem lattice_subset (value : FiniteAdelesˣ) (integral : value.val ∈ Set.range integralEmbedding) :
    lattice value ⊆ Set.range integralEmbedding := by
  obtain ⟨integer, equality⟩ := integral
  rintro _ ⟨other, rfl⟩
  exact ⟨integer * other, by rw [map_mul, equality]⟩

theorem norm_le_one (value : FiniteAdelesˣ) (integral : value.val ∈ Set.range integralEmbedding) :
    (adeleNorm (Norm.finiteAdeleUnit value) : ℝ) ≤ 1 := by
  have inequality := measure_mono (μ := finiteMeasure) (lattice_subset value integral)
  rw [lattice_measure, finiteMeasure_integralLattice] at inequality
  exact_mod_cast inequality

theorem integralUnit_of_norm_one (value : FiniteAdelesˣ)
    (integral : value.val ∈ Set.range integralEmbedding)
    (normOne : (adeleNorm (Norm.finiteAdeleUnit value) : ℝ) = 1) :
    ∃ unit : IntegralAdelesˣ, Units.map integralEmbedding.toMonoidHom unit = value := by
  have measureOne : finiteMeasure (lattice value) = 1 := by
    rw [lattice_measure]
    exact_mod_cast normOne
  have differenceZero : finiteMeasure (Set.range integralEmbedding \ lattice value) = 0 := by
    rw [measure_sdiff (lattice_subset value integral) (lattice_open value).measurableSet.nullMeasurableSet
      (lattice_compact value).measure_lt_top.ne, finiteMeasure_integralLattice, measureOne, tsub_self]
  have oneIn : (1 : FiniteAdeles) ∈ lattice value := by
    by_contra outside
    have positive := (integralLattice_isOpen.inter (lattice_compact value).isClosed.isOpen_compl).measure_pos finiteMeasure
      ⟨1, ⟨1, map_one integralEmbedding⟩, outside⟩
    change 0 < finiteMeasure (Set.range integralEmbedding \ lattice value) at positive
    rw [differenceZero] at positive
    exact (lt_irrefl (0 : ENNReal)) positive
  obtain ⟨inverse, inverseValue⟩ := oneIn
  have inverseEquality : integralEmbedding inverse = value.inv := by
    have equality := congrArg (fun scalar : FiniteAdeles => value.inv * scalar) inverseValue
    simpa only [← mul_assoc, value.inv_val, one_mul, mul_one] using equality
  obtain ⟨integer, integerValue⟩ := integral
  let unit : IntegralAdelesˣ := ⟨integer, inverse,
    integralEmbedding_injective (by rw [map_mul, integerValue, inverseEquality, value.val_inv, map_one]),
    integralEmbedding_injective (by rw [map_mul, inverseEquality, integerValue, value.inv_val, map_one])⟩
  exact ⟨unit, Units.ext integerValue⟩

theorem norm_lt_one (value : FiniteAdelesˣ) (integral : value.val ∈ Set.range integralEmbedding)
    (nonunit : value ∉ Set.range (Units.map integralEmbedding.toMonoidHom)) :
    (adeleNorm (Norm.finiteAdeleUnit value) : ℝ) < 1 :=
  lt_of_le_of_ne (norm_le_one value integral)
    (fun equality => nonunit (integralUnit_of_norm_one value integral equality))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralIdeleNorm
