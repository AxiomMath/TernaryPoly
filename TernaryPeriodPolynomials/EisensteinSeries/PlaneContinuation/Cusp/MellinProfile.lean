module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.CuspDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellinProfile

def reflection {ring : Type*} [CommRing ring] : GeneralLinearGroup (Fin 2) ring :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem reflection_map {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) : GeneralLinearGroup.map hom reflection = reflection := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [reflection, GeneralLinearGroup.map_apply]

theorem reflection_adelic : GeneralLinearGroup.map rationalAdele (reflection : BinaryRationalGL) =
    atFinite (GeneralLinearGroup.map integralEmbedding (reflection : IntegralBinaryGL)) *
      atInfinity (reflection : BinaryRealGL) := by
  rw [BinaryAdelicReduction.rational_decomposition, reflection_map, reflection_map, reflection_map,
    FiniteLevel.atFinite_atInfinity_commute]

def heightMatrix (height : ℝ) : BinaryMatrix := !![height, 0; 0, 1]

noncomputable def heightUnit (height : ℝ) (positive : 0 < height) : BinaryRealGL :=
  unit (Complex.I * height) (by simpa using positive)

theorem heightUnit_val (height : ℝ) (positive : 0 < height) :
    (heightUnit height positive).val = heightMatrix height := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [heightUnit, unit, matrix, heightMatrix]

noncomputable def profile (data : CuspidalRepresentation) (vector : data.smooth)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (height : ℝ) : ℂ :=
  scalarMatrixOrbit data (atFinite (GeneralLinearGroup.map integralEmbedding point)) vector
    (heightMatrix height * right.val)

theorem profile_eq (data : CuspidalRepresentation) (vector : data.smooth)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (height : ℝ) (positive : 0 < height) :
    profile data vector point right height = data.realize vector
      (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity (heightUnit height positive * right)) := by
  unfold profile scalarMatrixOrbit
  rw [← heightUnit_val height positive]
  change data.realize vector (_ * atInfinity (invertibleMatrix (heightUnit height positive * right).val)) = _
  rw [invertibleMatrix_units]

theorem profile_continuousOn (data : CuspidalRepresentation) (vector : data.smooth)
    (point : IntegralBinaryGL) (right : BinaryRealGL) :
    ContinuousOn (profile data vector point right) (Set.Ioi 0) := by
  have continuousMatrix : Continuous heightMatrix := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp [heightMatrix] <;> fun_prop
  exact (scalarMatrixOrbit_contDiffOn data
    (atFinite (GeneralLinearGroup.map integralEmbedding point)) vector).continuousOn.comp
      (continuousMatrix.matrix_mul continuous_const).continuousOn
      (fun height positive => by
        change (heightMatrix height * right.val).det ≠ 0
        rw [← heightUnit_val height positive]
        exact GeneralLinearGroup.det_ne_zero (heightUnit height positive * right))

theorem reflection_height (height : ℝ) (positive : 0 < height) (right : BinaryRealGL) :
    reflection * heightUnit height positive * right =
      (heightUnit height⁻¹ (inv_pos.mpr positive) * reflection * right) *
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 height (ne_of_gt positive)) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Units.val_mul, heightUnit_val, reflection, heightMatrix, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> field_simp [ne_of_gt positive]

theorem realize_positive_scalar {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (point : BinaryAdelicGL) (height : ℝ) (positive : 0 < height) :
    data.cusp.realize vector (point * atInfinity
      (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 height (ne_of_gt positive)))) =
        data.cusp.realize vector point := by
  rw [← smoothTranslate_realize]
  have equality : smoothTranslate data.cusp
      (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 height (ne_of_gt positive))) vector = vector := by
    apply Subtype.ext
    exact CohomologicalCenter.positiveReal_scalar_fixed data _ positive vector.val
  rw [equality]

theorem profile_inversion {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (height : ℝ) (positive : 0 < height) :
    profile data.cusp vector point right height =
      profile data.cusp vector (reflection * point) (reflection * right) height⁻¹ := by
  rw [profile_eq data.cusp vector point right height positive,
    profile_eq data.cusp vector (reflection * point) (reflection * right) height⁻¹ (inv_pos.mpr positive)]
  rw [← data.cusp.leftRational (reflection : BinaryRationalGL) vector]
  rw [reflection_adelic]
  have factorization : atFinite (GeneralLinearGroup.map integralEmbedding reflection) * atInfinity reflection *
      (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity (heightUnit height positive * right)) =
      atFinite (GeneralLinearGroup.map integralEmbedding (reflection * point)) *
        atInfinity (reflection * heightUnit height positive * right) := by
    rw [map_mul, FiniteLevel.atFinite_mul, Height.atInfinity_mul, Height.atInfinity_mul]
    rw [← mul_assoc, mul_assoc (atFinite _) (atInfinity _), ← FiniteLevel.atFinite_atInfinity_commute]
    simp only [Height.atInfinity_mul, mul_assoc]
  rw [factorization, reflection_height, Height.atInfinity_mul, ← mul_assoc,
    realize_positive_scalar data vector _ height positive]
  simp only [mul_assoc]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellinProfile
