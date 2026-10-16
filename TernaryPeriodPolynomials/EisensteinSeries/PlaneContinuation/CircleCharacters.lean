module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.HolomorphicRealization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CircleCharacters

theorem exists_parameter (value : Circle) : ∃ parameter : Parameter, parameter.toCircle = value := by
  refine ⟨((value : ℂ).arg / (2 * Real.pi) : ℝ), ?_⟩
  rw [AddCircle.toCircle_apply_mk, div_one]
  have equality : 2 * Real.pi * ((value : ℂ).arg / (2 * Real.pi)) = (value : ℂ).arg := by
    field_simp
  rw [equality, Circle.exp_arg]

theorem fourier_zpow (index : ℤ) (parameter : Parameter) :
    fourier index parameter = (parameter.toCircle : ℂ) ^ index := by
  change (((index • parameter).toCircle : Circle) : ℂ) = _
  rw [AddCircle.toCircle_zsmul, Circle.coe_zpow]

theorem circle_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) (value : Circle) :
    data.π (atInfinity (circleRotation value)) vector.val = (value : ℂ) ^ index • vector.val := by
  obtain ⟨parameter, rfl⟩ := exists_parameter value
  have equality := (rotation_eigen_iff data vector index).mp eigen parameter
  rw [fourier_zpow] at equality
  exact equality

theorem realize_circle (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector)
    (point : BinaryAdelicGL) (value : Circle) :
    data.realize vector (point * atInfinity (circleRotation value)) =
      (value : ℂ) ^ index * data.realize vector point := by
  rw [← smoothTranslate_realize]
  have equality : smoothTranslate data (circleRotation value) vector = (value : ℂ) ^ index • vector :=
    Subtype.ext (circle_eigen data vector index eigen value)
  rw [equality, map_smul, Pi.smul_apply, smul_eq_mul]

noncomputable def complexUnit (value : ℂ) (nonzero : value ≠ 0) : BinaryRealGL :=
  Units.map complexMatrix.toMonoidHom (Units.mk0 value nonzero)

theorem complexUnit_val (value : ℂ) (nonzero : value ≠ 0) :
    (complexUnit value nonzero).val = complexMatrix value := rfl

noncomputable def phase (value : ℂ) (nonzero : value ≠ 0) : Circle :=
  ⟨value / (‖value‖ : ℂ), by
    change value / (‖value‖ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_iff_norm, sub_zero]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr nonzero)]⟩

theorem complexUnit_factor (value : ℂ) (nonzero : value ≠ 0) :
    complexUnit value nonzero =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ‖value‖ (norm_ne_zero_iff.mpr nonzero)) *
        circleRotation (phase value nonzero) := by
  apply Units.ext
  change complexMatrix value =
    (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ‖value‖ (norm_ne_zero_iff.mpr nonzero))).val *
      (circleRotation (phase value nonzero)).val
  rw [circleRotation_val]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [complexMatrix, phase, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.div_ofReal_re, Complex.div_ofReal_im] <;> field_simp [norm_ne_zero_iff.mpr nonzero]

theorem realize_complexUnit {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) (index : ℤ)
    (eigen : rotationOperator data.cusp vector = (Complex.I * index) • vector)
    (point : BinaryAdelicGL) (value : ℂ) (nonzero : value ≠ 0) :
    data.cusp.realize vector (point * atInfinity (complexUnit value nonzero)) =
      (value / (‖value‖ : ℂ)) ^ index * data.cusp.realize vector point := by
  rw [complexUnit_factor, Height.atInfinity_mul, ← mul_assoc, realize_circle data.cusp vector index eigen]
  have fixed : smoothTranslate data.cusp
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ‖value‖ (norm_ne_zero_iff.mpr nonzero))) vector = vector :=
    Subtype.ext (CohomologicalCenter.positiveReal_scalar_fixed data _ (norm_pos_iff.mpr nonzero) vector.val)
  rw [← smoothTranslate_realize, fixed]
  rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CircleCharacters
