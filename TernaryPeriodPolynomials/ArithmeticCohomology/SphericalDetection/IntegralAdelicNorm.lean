module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Representation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteAdeleUnit (unit : FiniteAdelesˣ) : Adelesˣ where
  val := (1, unit.val)
  inv := (1, unit.inv)
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem integralUnit_mul_mem_lattice (unit : IntegralAdelesˣ) (point : FiniteAdeles) :
    integralEmbedding unit.val * point ∈ Set.range integralEmbedding ↔
      point ∈ Set.range integralEmbedding := by
  constructor
  · rintro ⟨integral, equality⟩
    refine ⟨unit.inv * integral, ?_⟩
    rw [map_mul, equality, ← mul_assoc, ← map_mul, unit.inv_val, map_one, one_mul]
  · rintro ⟨integral, rfl⟩
    exact ⟨unit.val * integral, map_mul _ _ _⟩

theorem adeleNorm_finiteIntegralUnit (unit : IntegralAdelesˣ) :
    (adeleNorm (finiteAdeleUnit (Units.map integralEmbedding unit)) : ℝ) = 1 := by
  let box : Set Adeles := Set.Icc (0 : ℝ) 1 ×ˢ Set.range integralEmbedding
  have preimage : (ContinuousAddEquiv.mulLeft (finiteAdeleUnit (Units.map integralEmbedding unit))) ⁻¹' box = box := by
    ext point
    change (0 ≤ 1 * point.1 ∧ 1 * point.1 ≤ 1) ∧
      integralEmbedding unit.val * point.2 ∈ Set.range integralEmbedding ↔
      (0 ≤ point.1 ∧ point.1 ≤ 1) ∧ point.2 ∈ Set.range integralEmbedding
    rw [one_mul, integralUnit_mul_mem_lattice]
  have volume : adeleMeasure box = 1 := by
    rw [adeleMeasure, Measure.prod_prod, finiteMeasure_integralLattice]
    norm_num
  have scale := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := box) (ContinuousAddEquiv.mulLeft (finiteAdeleUnit (Units.map integralEmbedding unit)))
  rw [preimage, volume] at scale
  change (adeleNorm (finiteAdeleUnit (Units.map integralEmbedding unit)) : ℝ≥0∞) * 1 = 1 at scale
  have real_scale := congrArg ENNReal.toReal scale
  simpa only [mul_one, ENNReal.coe_toReal, ENNReal.toReal_one] using real_scale

theorem normPower_finiteIntegralUnit (unit : IntegralAdelesˣ) (exponent : ℂ) :
    normPower (finiteAdeleUnit (Units.map integralEmbedding unit)) exponent = 1 := by
  rw [normPower, adeleNorm_finiteIntegralUnit, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem binary_det_atFinite (matrix : BinaryFiniteGL) :
    GeneralLinearGroup.det (atFinite matrix) = finiteAdeleUnit (GeneralLinearGroup.det matrix) := by
  apply Units.ext
  apply Prod.ext <;>
    simp [GeneralLinearGroup.val_det_apply, atFinite, combineGL, pairMatrix, finiteAdeleUnit, Matrix.det_fin_two]

theorem binary_det_map {R S : Type*} [CommRing R] [CommRing S] (map : R →+* S)
    (matrix : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.det (GeneralLinearGroup.map map matrix) = Units.map map (GeneralLinearGroup.det matrix) := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem normPower_binaryFiniteIntegral (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding matrix))) exponent = 1 := by
  rw [binary_det_atFinite, binary_det_map, normPower_finiteIntegralUnit]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
