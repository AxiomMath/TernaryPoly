module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped NNReal ENNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm

theorem adeleMeasure_additiveDomain : adeleMeasure additiveDomain = 1 := by
  rw [adeleMeasure, additiveDomain, Measure.prod_prod,
    finiteMeasure_integralLattice, Real.volume_Ico]
  norm_num

theorem adeleNorm_real_positive (t : ℝˣ) (ht : 0 < t.val) :
    (adeleNorm (realAdeleUnit t) : ℝ) = t.val := by
  have hpreimage :
      (ContinuousAddEquiv.mulLeft (realAdeleUnit t)) ⁻¹' additiveDomain =
        Set.Ico 0 (1 / t.val) ×ˢ Set.range integralEmbedding := by
    ext x
    change (0 ≤ t.val * x.1 ∧ t.val * x.1 < 1) ∧
      (1 : FiniteAdeles) * x.2 ∈ Set.range integralEmbedding ↔ _
    simp only [one_mul, Set.mem_prod, Set.mem_Ico]
    rw [mul_comm t.val x.1, ← div_le_iff₀ ht, ← lt_div_iff₀ ht, zero_div]
  have hmeasure := addEquivAddHaarChar_smul_preimage adeleMeasure
    (ContinuousAddEquiv.mulLeft (realAdeleUnit t)) (X := additiveDomain)
  rw [hpreimage, adeleMeasure_additiveDomain, adeleMeasure, Measure.prod_prod,
    finiteMeasure_integralLattice, Real.volume_Ico, sub_zero, mul_one] at hmeasure
  change (adeleNorm (realAdeleUnit t) : ℝ≥0∞) * ENNReal.ofReal (1 / t.val) = 1 at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal
    (one_div_nonneg.mpr ht.le), ENNReal.toReal_one] at hreal
  have hdivision : (adeleNorm (realAdeleUnit t) : ℝ) / t.val = 1 := by
    simpa only [mul_one_div] using hreal
  have hproduct := (div_eq_iff (ne_of_gt ht)).mp hdivision
  nlinarith

theorem realAdeleUnit_mul (first second : ℝˣ) :
    realAdeleUnit (first * second) = realAdeleUnit first * realAdeleUnit second := by
  apply Units.ext
  simp [realAdeleUnit]

theorem adeleNorm_real_neg_one :
    (adeleNorm (realAdeleUnit (-1 : ℝˣ)) : ℝ) = 1 := by
  have squareIdentity :
      realAdeleUnit (-1 : ℝˣ) * realAdeleUnit (-1 : ℝˣ) = 1 := by
    apply Units.ext
    simp [realAdeleUnit]
  have normIdentity := congrArg (fun unit => (adeleNorm unit : ℝ)) squareIdentity
  simp only [map_mul, NNReal.coe_mul, map_one, NNReal.coe_one] at normIdentity
  have positiveNorm : 0 < (adeleNorm (realAdeleUnit (-1 : ℝˣ)) : ℝ) :=
    adeleNorm_pos _
  nlinarith

theorem adeleNorm_real (unit : ℝˣ) :
    (adeleNorm (realAdeleUnit unit) : ℝ) = |unit.val| := by
  by_cases positiveUnit : 0 < unit.val
  · rw [adeleNorm_real_positive unit positiveUnit, abs_of_pos positiveUnit]
  · have negativeUnit : unit.val < 0 := lt_of_le_of_ne (le_of_not_gt positiveUnit)
      (Units.ne_zero unit)
    have positiveNegative : 0 < (-unit).val := by
      simpa only [Units.val_neg] using neg_pos.mpr negativeUnit
    have unitFactorization : (-1 : ℝˣ) * (-unit) = unit := by
      apply Units.ext
      simp
    rw [← unitFactorization, realAdeleUnit_mul, map_mul, NNReal.coe_mul,
      adeleNorm_real_neg_one, one_mul, adeleNorm_real_positive (-unit) positiveNegative,
      Units.val_neg, unitFactorization, abs_of_neg negativeUnit]

theorem det_atInfinity {matrixSize : ℕ}
    (realMatrix : Matrix.GeneralLinearGroup (Fin matrixSize) ℝ) :
    Matrix.GeneralLinearGroup.det (atInfinity realMatrix) =
      realAdeleUnit (Matrix.GeneralLinearGroup.det realMatrix) := by
  apply Units.ext
  apply Prod.ext
  · change (RingHom.fst ℝ FiniteAdeles) (atInfinity realMatrix).val.det = realMatrix.val.det
    rw [RingHom.map_det]
    rfl
  · change (RingHom.snd ℝ FiniteAdeles) (atInfinity realMatrix).val.det = 1
    rw [RingHom.map_det]
    change (1 : Matrix (Fin matrixSize) (Fin matrixSize) FiniteAdeles).det = 1
    exact Matrix.det_one

theorem adeleNorm_det_atInfinity {matrixSize : ℕ}
    (realMatrix : Matrix.GeneralLinearGroup (Fin matrixSize) ℝ) :
    (adeleNorm (Matrix.GeneralLinearGroup.det (atInfinity realMatrix)) : ℝ) =
      |realMatrix.val.det| := by
  rw [det_atInfinity, adeleNorm_real]
  rfl

noncomputable def finiteAdeleUnit (unit : FiniteAdelesˣ) : Adelesˣ where
  val := (1, unit.val)
  inv := (1, unit.inv)
  val_inv := by
    change (1 * 1, unit.val * unit.inv) = (1, 1)
    simp
  inv_val := by
    change (1 * 1, unit.inv * unit.val) = (1, 1)
    simp

theorem integralUnit_mul_mem_lattice (unit : IntegralAdelesˣ) (value : FiniteAdeles) :
    integralEmbedding unit.val * value ∈ Set.range integralEmbedding ↔
      value ∈ Set.range integralEmbedding := by
  constructor
  · rintro ⟨preimage, preimageValue⟩
    refine ⟨unit.inv * preimage, ?_⟩
    rw [map_mul, preimageValue, ← mul_assoc, ← map_mul, unit.inv_val, map_one, one_mul]
  · rintro ⟨preimage, rfl⟩
    exact ⟨unit.val * preimage, map_mul integralEmbedding _ _⟩

theorem adeleNorm_integralUnit (unit : IntegralAdelesˣ) :
    adeleNorm (finiteAdeleUnit (Units.map integralEmbedding.toMonoidHom unit)) = 1 := by
  have domainPreimage : (ContinuousAddEquiv.mulLeft
      (finiteAdeleUnit (Units.map integralEmbedding.toMonoidHom unit))) ⁻¹'
      additiveDomain = additiveDomain := by
    ext value
    change ((0 ≤ 1 * value.1 ∧ 1 * value.1 < 1) ∧
        integralEmbedding unit.val * value.2 ∈ Set.range integralEmbedding) ↔
      (0 ≤ value.1 ∧ value.1 < 1) ∧ value.2 ∈ Set.range integralEmbedding
    rw [one_mul, integralUnit_mul_mem_lattice]
  have measureIdentity := addEquivAddHaarChar_smul_preimage adeleMeasure
    (ContinuousAddEquiv.mulLeft
      (finiteAdeleUnit (Units.map integralEmbedding.toMonoidHom unit))) (X := additiveDomain)
  rw [domainPreimage, adeleMeasure_additiveDomain] at measureIdentity
  change (adeleNorm (finiteAdeleUnit (Units.map integralEmbedding.toMonoidHom unit)) : ℝ≥0∞) *
    1 = 1 at measureIdentity
  exact_mod_cast (mul_one _).symm.trans measureIdentity

theorem det_atFinite {matrixSize : ℕ}
    (finiteMatrix : Matrix.GeneralLinearGroup (Fin matrixSize) FiniteAdeles) :
    Matrix.GeneralLinearGroup.det (atFinite finiteMatrix) =
      finiteAdeleUnit (Matrix.GeneralLinearGroup.det finiteMatrix) := by
  apply Units.ext
  apply Prod.ext
  · change (RingHom.fst ℝ FiniteAdeles) (atFinite finiteMatrix).val.det = 1
    rw [RingHom.map_det]
    exact Matrix.det_one
  · change (RingHom.snd ℝ FiniteAdeles) (atFinite finiteMatrix).val.det = finiteMatrix.val.det
    rw [RingHom.map_det]
    rfl

theorem adeleNorm_det_integral {matrixSize : ℕ}
    (integralMatrix : Matrix.GeneralLinearGroup (Fin matrixSize) IntegralAdeles) :
    adeleNorm (Matrix.GeneralLinearGroup.det
      (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding integralMatrix))) = 1 := by
  rw [det_atFinite]
  have determinantMap : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map integralEmbedding integralMatrix) =
      Units.map integralEmbedding.toMonoidHom (Matrix.GeneralLinearGroup.det integralMatrix) := by
    apply Units.ext
    exact (RingHom.map_det integralEmbedding integralMatrix.val).symm
  rw [determinantMap, adeleNorm_integralUnit]

theorem combineGL_eq_mul {matrixSize : ℕ}
    (realMatrix : Matrix.GeneralLinearGroup (Fin matrixSize) ℝ)
    (finiteMatrix : Matrix.GeneralLinearGroup (Fin matrixSize) FiniteAdeles) :
    combineGL realMatrix finiteMatrix = atInfinity realMatrix * atFinite finiteMatrix := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · simp only [Units.val_mul, atInfinity, atFinite, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.fst_sum, Prod.fst_mul]
    exact (congrArg (fun matrix : Matrix (Fin matrixSize) (Fin matrixSize) ℝ =>
      matrix row column) (mul_one realMatrix.val)).symm
  · simp only [Units.val_mul, atInfinity, atFinite, combineGL, pairMatrix, Matrix.mul_apply,
      Prod.snd_sum, Prod.snd_mul]
    exact (congrArg (fun matrix : Matrix (Fin matrixSize) (Fin matrixSize) FiniteAdeles =>
      matrix row column) (one_mul finiteMatrix.val)).symm

theorem adelicGL_eq_mul (matrix : AdelicGL) :
    matrix = atInfinity (realGroup matrix) * atFinite (finiteGroup matrix) := by
  rw [← combineGL_eq_mul]
  apply Units.ext
  rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm
