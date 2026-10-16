module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Fourier
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Differentiation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FourierDifferentiation
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation

noncomputable def complexLinear : ℂ →L[ℝ] BinaryMatrix where
  toFun := complexMatrix
  map_add' := map_add complexMatrix
  map_smul' scalar value := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [complexMatrix, mul_neg]
  cont := complexMatrix_continuous

noncomputable def generator : BinaryMatrix := complexMatrix ((2 * Real.pi : ℝ) * Complex.I)

theorem rotation_val_exp (time : ℝ) :
    (rotation (time : Parameter)).val = complexMatrix (Complex.exp ((2 * Real.pi * time : ℝ) * Complex.I)) := by
  rw [rotation, circleRotation_val, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]

theorem rotation_hasDerivAt (time : ℝ) :
    HasDerivAt (fun time : ℝ => (rotation (time : Parameter)).val)
      ((rotation (time : Parameter)).val * generator) time := by
  have linearDerivative : HasDerivAt (fun point : ℝ => (↑(2 * Real.pi * point) : ℂ) * Complex.I)
      ((↑(2 * Real.pi) : ℂ) * Complex.I) time := by
    convert (((hasDerivAt_id time).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I) using 1
    · rfl
    · rw [mul_one]
  have exponentialDerivative : HasDerivAt
      (fun point : ℝ => Complex.exp ((↑(2 * Real.pi * point) : ℂ) * Complex.I))
      (Complex.exp ((↑(2 * Real.pi * time) : ℂ) * Complex.I) * (↑(2 * Real.pi) * Complex.I)) time :=
    linearDerivative.cexp
  have matrixDerivative : HasDerivAt
      (fun point : ℝ => complexLinear (Complex.exp ((↑(2 * Real.pi * point) : ℂ) * Complex.I)))
      (complexLinear (Complex.exp ((↑(2 * Real.pi * time) : ℂ) * Complex.I) *
        (↑(2 * Real.pi) * Complex.I))) time :=
    complexLinear.hasFDerivAt.comp_hasDerivAt time exponentialDerivative
  have curveEquality : (fun point : ℝ => (rotation (point : Parameter)).val) =
      (fun point : ℝ => complexLinear (Complex.exp ((↑(2 * Real.pi * point) : ℂ) * Complex.I))) :=
    funext rotation_val_exp
  have derivativeEquality : complexLinear (Complex.exp ((↑(2 * Real.pi * time) : ℂ) * Complex.I) *
      (↑(2 * Real.pi) * Complex.I)) = (rotation (time : Parameter)).val * generator := by
    change complexMatrix _ = _
    rw [map_mul, rotation_val_exp]
    rfl
  rw [curveEquality, ← derivativeEquality]
  exact matrixDerivative

noncomputable def rotationDerivative (data : CuspidalRepresentation) : data.smooth →ₗ[ℂ] data.smooth :=
  directionalOperator data generator

theorem orbit_hasDerivAt (data : CuspidalRepresentation) (vector : data.smooth) (time : ℝ) :
    HasDerivAt (fun time : ℝ => data.π (atInfinity (rotation (time : Parameter))) vector.val)
      (data.π (atInfinity (rotation (time : Parameter))) (rotationDerivative data vector).val) time := by
  have regularity := TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_analyticAt_of_one data vector.val
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.smooth_orbit_contDiffAt_one data vector).analyticAt (rotation (time : Parameter))
  have smoothness : ContDiffAt ℝ ⊤ (realOrbit data vector.val) (rotation (time : Parameter)).val :=
    regularity.contDiffAt
  have differentiability : DifferentiableAt ℝ (realOrbit data vector.val) (rotation (time : Parameter)).val :=
    smoothness.differentiableAt (by simp)
  have derivative := differentiability.hasFDerivAt.comp_hasDerivAt time (rotation_hasDerivAt time)
  have curveEquality : realOrbit data vector.val ∘ (fun time : ℝ => (rotation (time : Parameter)).val) =
      (fun time : ℝ => data.π (atInfinity (rotation (time : Parameter))) vector.val) := by
    funext time
    change data.π (atInfinity (invertibleMatrix (rotation (time : Parameter)).val)) vector.val = _
    rw [invertibleMatrix_units]
  rw [curveEquality] at derivative
  have tangentEquality : data.π (atInfinity (rotation (time : Parameter))) (rotationDerivative data vector).val =
      fderiv ℝ (realOrbit data vector.val) (rotation (time : Parameter)).val
        ((rotation (time : Parameter)).val * generator) :=
    directionalVector_translate data vector generator (rotation (time : Parameter))
  exact (congrArg (fun tangent : data.H => HasDerivAt
    (fun point : ℝ => data.π (atInfinity (rotation (point : Parameter))) vector.val) tangent time)
      tangentEquality).mpr derivative

theorem rotationDerivative_preserves_fixed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : data.smooth) (fixed : vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    (rotationDerivative data vector).val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level :=
  directionalOperator_preserves_fixed data level generator vector fixed

theorem modeVector_rotationDerivative (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ) :
    RotationFourier.modeVector data index (rotationDerivative data vector).val =
      FourierDifferentiation.frequency index • RotationFourier.modeVector data index vector.val :=
  FourierDifferentiation.fourierCoeff_derivative _ _
    (RotationFourier.orbit_continuous data (rotationDerivative data vector).val)
    (orbit_hasDerivAt data vector) index

theorem modeVector_iteratedDerivative (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (order : ℕ) :
    RotationFourier.modeVector data index ((rotationDerivative data ^ order) vector).val =
      FourierDifferentiation.frequency index ^ order • RotationFourier.modeVector data index vector.val := by
  induction order with
  | zero => simp
  | succ order inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, modeVector_rotationDerivative, inductionHypothesis,
        smul_smul, pow_succ']

/-- Every rotation derivative gives an unconditional polynomial bound on the Hilbert Fourier coefficients. -/
theorem modeVector_frequency_norm_bound (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (order : ℕ) :
    ‖FourierDifferentiation.frequency index‖ ^ order * ‖RotationFourier.modeVector data index vector.val‖ ≤
      ‖((rotationDerivative data ^ order) vector).val‖ := by
  have estimate := RotationFourier.modeVector_norm_le data index ((rotationDerivative data ^ order) vector).val
  rw [modeVector_iteratedDerivative, norm_smul, norm_pow] at estimate
  exact estimate

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation
