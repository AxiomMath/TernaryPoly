module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Coordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationConvolution TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifference
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationPrimitive

noncomputable def coefficients (target index : ℤ) : ℂ := ((frequency (-index) - frequency target) ^ 2)⁻¹

theorem coefficients_norm (target index : ℤ) :
    ‖coefficients target index‖ = ((2 * Real.pi) ^ 2)⁻¹ * (1 / (((-index - target : ℤ) : ℝ) ^ 2)) := by
  simp only [coefficients, norm_inv, norm_pow, RotationKernel.frequency_sub_norm, mul_pow,
    sq_abs, mul_inv_rev, one_div, mul_comm]

theorem coefficients_summable (target : ℤ) : Summable (fun index => ‖coefficients target index‖) := by
  have series : Summable (fun index : ℤ => (1 : ℝ) / (index : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have injective : Function.Injective (fun index : ℤ => -index - target) := by
    intro first second equality
    exact neg_injective (sub_left_injective equality)
  have shifted := (series.comp_injective injective).mul_left (((2 * Real.pi) ^ 2)⁻¹)
  simp only [coefficients_norm]
  exact shifted

noncomputable def kernel (target : ℤ) : C(Parameter, ℂ) := FourierSeriesKernel.kernel (coefficients target)

theorem multiplier (target index : ℤ) (different : index ≠ target) :
    (frequency index - frequency target) * fourierCoeff (kernel target) (-index) *
      (frequency index - frequency target) = 1 := by
  rw [kernel, FourierSeriesKernel.kernel_fourierCoeff _ (coefficients_summable target), coefficients, neg_neg]
  have nonzero : frequency index - frequency target ≠ 0 :=
    sub_ne_zero.mpr (fun equality => different (SmallDivisorKernel.frequency_injective equality))
  field_simp

noncomputable def primitive (data : CuspidalRepresentation) (target : ℤ) (vector : data.smooth) : data.smooth :=
  smoothConvolution data (kernel target) (shiftedDerivative data target vector)

/-- An actual analytic primitive of the shifted rotation derivative away from its resonant mode. -/
theorem primitive_identity (data : CuspidalRepresentation) (target : ℤ) (vector : data.smooth) :
    shiftedDerivative data target (primitive data target vector) = vector - smoothMode data target vector := by
  apply Subtype.ext
  apply eq_of_modes data
  intro index
  change modeVector data index (shiftedDerivative data target (primitive data target vector)).val =
    modeOperator data index (vector.val - modeVector data target vector.val)
  rw [modeVector_shiftedDerivative, map_sub, modeOperator_apply, modeOperator_apply, modeVector_comp]
  by_cases same : index = target
  · subst index
    simp
  · have modePrimitive : modeVector data index (primitive data target vector).val =
        fourierCoeff (kernel target) (-index) • ((frequency index - frequency target) • modeVector data index vector.val) := by
      change modeVector data index (convolutionVector data (kernel target) (shiftedDerivative data target vector).val) = _
      rw [modeVector_convolution, modeVector_shiftedDerivative]
    rw [modePrimitive, smul_smul, smul_smul, multiplier target index same]
    simp [same]

theorem primitive_fixed (data : CuspidalRepresentation) (target : ℤ) (vector : data.smooth)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL)) (fixed : vector.val ∈ fixedSubspace data level) :
    (primitive data target vector).val ∈ fixedSubspace data level := by
  apply (convolutionVector_preserves_fixedSmooth data (kernel target) level openness compactness
    (shiftedDerivative data target vector) ?_).2
  exact (fixedSubspace data level).sub_mem (rotationDerivative_preserves_fixed data level vector fixed)
    ((fixedSubspace data level).smul_mem _ fixed)

noncomputable def rotationPrimitive (data : CuspidalRepresentation) (target : ℤ) (vector : data.smooth) : data.smooth :=
  (2 * Real.pi : ℂ) • primitive data target vector

theorem rotationPrimitive_identity (data : CuspidalRepresentation) (target : ℤ) (vector : data.smooth) :
    LieOperators.rotationOperator data (rotationPrimitive data target vector) -
      (Complex.I * target) • rotationPrimitive data target vector = vector - smoothMode data target vector := by
  have equality : LieOperators.rotationOperator data (rotationPrimitive data target vector) -
      (Complex.I * target) • rotationPrimitive data target vector =
        shiftedDerivative data target (primitive data target vector) := by
    simp only [rotationPrimitive, shiftedDerivative, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LieOperators.rotationDerivative_eq, map_smul, smul_smul, frequency]
    module
  exact equality.trans (primitive_identity data target vector)

theorem rotationPrimitive_fixed (data : CuspidalRepresentation) (target : ℤ) (vector : data.smooth)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL)) (fixed : vector.val ∈ fixedSubspace data level) :
    (rotationPrimitive data target vector).val ∈ fixedSubspace data level :=
  (fixedSubspace data level).smul_mem _ (primitive_fixed data target vector level openness compactness fixed)

theorem smoothMode_shifted_zero (data : CuspidalRepresentation) (target : ℤ) (vector : data.smooth) :
    smoothMode data target (LieOperators.rotationOperator data vector - (Complex.I * target) • vector) = 0 := by
  have equality : smoothMode data target (rotationDerivative data vector) =
      frequency target • smoothMode data target vector := Subtype.ext (modeVector_rotationDerivative data vector target)
  rw [LieOperators.rotationDerivative_eq, LinearMap.smul_apply, map_smul] at equality
  have nonzero : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  apply (smul_right_inj (M := data.smooth) (r := (2 * Real.pi : ℂ)) nonzero).mp
  rw [smul_zero]
  simp only [map_sub, map_smul, smul_sub]
  rw [equality]
  have frequencyEquality : frequency target = (2 * Real.pi : ℂ) * (Complex.I * target) := by unfold frequency; ring
  rw [frequencyEquality, mul_smul, sub_self]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationPrimitive
