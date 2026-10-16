module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.WeightedAbsoluteTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryStrongApproximation TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.IdeleSlice

def rational : ℚˣ →* Adelesˣ := Units.map rationalAdele.toMonoidHom

def slice : Set Adelesˣ := {value | value.val.1 = (adeleNorm value : ℝ)}

theorem slice_measurable : MeasurableSet slice :=
  measurableSet_eq_fun (continuous_fst.comp (Units.continuous_val (M := Adeles))).measurable
    AdelicNormMeasurable.norm_measurable

theorem norm_rational_mul (scalar : ℚˣ) (value : Adelesˣ) :
    adeleNorm (rational scalar * value) = adeleNorm value := by
  rw [map_mul, rational, ProductFormula.adeleNorm_rational, one_mul]

theorem real_rational_mul (scalar : ℚˣ) (value : Adelesˣ) :
    (rational scalar * value).val.1 = (scalar.val : ℝ) * value.val.1 := rfl

theorem diagonal_det {ring : Type*} [CommRing ring] (first second : ringˣ) :
    GeneralLinearGroup.det (diagonal first second) = first * second := by
  apply Units.ext
  simp [BinaryStrongApproximation.diagonal, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem integral_real_det_mem (integral : IntegralBinaryGL) (realMatrix : BinaryRealGL)
    (positive : 0 < (GeneralLinearGroup.det realMatrix).val) :
    GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity realMatrix) ∈ slice := by
  change (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity realMatrix)).val.1 = _
  rw [map_mul, map_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_integral, one_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.det_atFinite, GeneralLinearGroup.map_det, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.det_atInfinity,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real_positive _ positive]
  change 1 * (GeneralLinearGroup.det realMatrix).val = (GeneralLinearGroup.det realMatrix).val
  exact one_mul _

theorem exists_representative (value : Adelesˣ) : ∃ scalar : ℚˣ, rational scalar * value ∈ slice := by
  obtain ⟨matrix, integral, realMatrix, positive, equality⟩ :=
    BinaryAdelicReduction.exists_rational_integral_positive (diagonal value 1)
  have determinant := congrArg GeneralLinearGroup.det equality
  rw [diagonal_det, mul_one, map_mul, GeneralLinearGroup.map_det] at determinant
  refine ⟨(GeneralLinearGroup.det matrix)⁻¹, ?_⟩
  rw [determinant]
  change (rational (GeneralLinearGroup.det matrix))⁻¹ *
    (rational (GeneralLinearGroup.det matrix) * _) ∈ slice
  rw [inv_mul_cancel_left]
  exact integral_real_det_mem integral realMatrix positive

theorem representative_unique (value : Adelesˣ) (first second : ℚˣ)
    (firstMem : rational first * value ∈ slice) (secondMem : rational second * value ∈ slice) : first = second := by
  have firstEq : (first.val : ℝ) * value.val.1 = (adeleNorm value : ℝ) := by
    simpa only [slice, Set.mem_ofPred_eq, real_rational_mul, norm_rational_mul] using firstMem
  have secondEq : (second.val : ℝ) * value.val.1 = (adeleNorm value : ℝ) := by
    simpa only [slice, Set.mem_ofPred_eq, real_rational_mul, norm_rational_mul] using secondMem
  have nonzero : value.val.1 ≠ 0 := (Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom value).ne_zero
  apply Units.ext
  exact_mod_cast mul_right_cancel₀ nonzero (firstEq.trans secondEq.symm)

theorem unique_representative (value : Adelesˣ) : ∃! scalar : ℚˣ, rational scalar * value ∈ slice := by
  obtain ⟨scalar, membership⟩ := exists_representative value
  exact ⟨scalar, membership, fun other otherMem => representative_unique value other scalar otherMem membership⟩

theorem rational_mul_mem_iff (value : Adelesˣ) (membership : value ∈ slice) (scalar : ℚˣ) :
    rational scalar * value ∈ slice ↔ scalar = 1 := by
  constructor
  · intro scalarMem
    exact representative_unique value scalar 1 scalarMem (by simpa only [map_one, one_mul] using membership)
  · rintro rfl
    simpa only [map_one, one_mul] using membership

def determinantSlice : Set BinaryAdelicGL := GeneralLinearGroup.det ⁻¹' slice

theorem determinantSlice_measurable : MeasurableSet determinantSlice :=
  slice_measurable.preimage WeightedAbsoluteTheta.determinant_continuous.measurable

theorem determinantSlice_mul (element point : BinaryAdelicGL) (determinant : GeneralLinearGroup.det element = 1) :
    element * point ∈ determinantSlice ↔ point ∈ determinantSlice := by
  change GeneralLinearGroup.det (element * point) ∈ slice ↔ GeneralLinearGroup.det point ∈ slice
  rw [map_mul, determinant, one_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.IdeleSlice
