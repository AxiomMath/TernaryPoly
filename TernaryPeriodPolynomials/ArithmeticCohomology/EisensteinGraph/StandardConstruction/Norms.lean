module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PlaneDecomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Norms

theorem additiveDomain_measure : adeleMeasure additiveDomain = 1 := by
  rw [adeleMeasure, additiveDomain, Measure.prod_prod, Real.volume_Ico,
    finiteMeasure_integralLattice]
  simp

theorem integralUnit_lattice_preimage (unit : IntegralAdelesˣ) :
    (fun value : FiniteAdeles => integralEmbedding unit.val * value) ⁻¹'
      Set.range integralEmbedding = Set.range integralEmbedding := by
  apply Set.ext
  intro value
  constructor
  · rintro ⟨integralValue, equality⟩
    refine ⟨unit.inv * integralValue, ?_⟩
    rw [map_mul, equality, ← mul_assoc, ← map_mul, unit.inv_val, map_one, one_mul]
  · rintro ⟨integralValue, rfl⟩
    exact ⟨unit.val * integralValue, map_mul _ _ _⟩

theorem integralUnit_domain_preimage (unit : IntegralAdelesˣ) :
    (ContinuousAddEquiv.mulLeft (integralAdeleUnit unit)) ⁻¹' additiveDomain =
      additiveDomain := by
  apply Set.ext
  intro value
  change ((1 : ℝ) * value.1 ∈ Set.Ico 0 1 ∧
    integralEmbedding unit.val * value.2 ∈ Set.range integralEmbedding) ↔
      value.1 ∈ Set.Ico 0 1 ∧ value.2 ∈ Set.range integralEmbedding
  rw [one_mul]
  have lattice := Set.ext_iff.mp (integralUnit_lattice_preimage unit) value.2
  exact and_congr Iff.rfl lattice

theorem integralUnit_norm (unit : IntegralAdelesˣ) : adeleNorm (integralAdeleUnit unit) = 1 := by
  have measureEquality := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := additiveDomain) (ContinuousAddEquiv.mulLeft (integralAdeleUnit unit))
  rw [integralUnit_domain_preimage, additiveDomain_measure] at measureEquality
  change adeleNorm (integralAdeleUnit unit) • (1 : ℝ≥0∞) = 1 at measureEquality
  simpa only [ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] using measureEquality

theorem realUnit_domain_preimage (unit : ℝˣ) :
    (ContinuousAddEquiv.mulLeft (realAdeleUnit unit)) ⁻¹' additiveDomain =
      ((fun value : ℝ => unit.val * value) ⁻¹' Set.Ico 0 1) ×ˢ
        Set.range integralEmbedding := by
  apply Set.ext
  intro value
  change (unit.val * value.1 ∈ Set.Ico 0 1 ∧
    (1 : FiniteAdeles) * value.2 ∈ Set.range integralEmbedding) ↔
      unit.val * value.1 ∈ Set.Ico 0 1 ∧ value.2 ∈ Set.range integralEmbedding
  rw [one_mul]

theorem realUnit_norm (unit : ℝˣ) : (adeleNorm (realAdeleUnit unit) : ℝ) = |unit.val| := by
  have measureEquality := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := additiveDomain) (ContinuousAddEquiv.mulLeft (realAdeleUnit unit))
  rw [additiveDomain_measure] at measureEquality
  rw [realUnit_domain_preimage, adeleMeasure, Measure.prod_prod,
    Real.volume_preimage_mul_left unit.ne_zero, finiteMeasure_integralLattice,
    Real.volume_Ico] at measureEquality
  change adeleNorm (realAdeleUnit unit) •
    (ENNReal.ofReal |unit.val⁻¹| * ENNReal.ofReal (1 - 0) * 1) = 1 at measureEquality
  simp only [sub_zero, ENNReal.ofReal_one, mul_one, ENNReal.smul_def, smul_eq_mul] at measureEquality
  have realEquality := congrArg ENNReal.toReal measureEquality
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at realEquality
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv] at realEquality
  exact (mul_inv_eq_one₀ (abs_ne_zero.mpr unit.ne_zero)).mp realEquality

theorem square_one_norm (unit : Adelesˣ) (square : unit * unit = 1) : adeleNorm unit = 1 := by
  have normSquare : adeleNorm unit * adeleNorm unit = 1 := by
    rw [← map_mul, square, map_one]
  have realSquare : (adeleNorm unit : ℝ) * (adeleNorm unit : ℝ) = 1 := by
    exact congrArg NNReal.toReal normSquare
  rcases mul_self_eq_one_iff.mp realSquare with positive | negative
  · exact NNReal.coe_injective positive
  · have nonnegative : (0 : ℝ) ≤ (adeleNorm unit : ℝ) := (adeleNorm unit).property
    exact False.elim (by linarith)

theorem rational_negative_one_norm :
    adeleNorm (Units.map rationalAdele (-1 : ℚˣ)) = 1 := by
  apply square_one_norm
  rw [← map_mul]
  simp

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Norms
