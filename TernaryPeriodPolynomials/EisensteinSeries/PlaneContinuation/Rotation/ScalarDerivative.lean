module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Scalar
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative

noncomputable def scalarMatrixOrbit (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (matrix : BinaryMatrix) : ℂ :=
  data.realize vector (point * atInfinity (invertibleMatrix matrix))

theorem scalarMatrixOrbit_contDiffOn (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) : ContDiffOn ℝ ⊤ (scalarMatrixOrbit data point vector) binaryDomain :=
  smooth_singleton (fun matrix => data.realize vector (point * atInfinity matrix))
    (data.scalarSmooth vector point)

noncomputable def scalarTangent (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (parameter : Parameter) : ℂ :=
  fderiv ℝ (scalarMatrixOrbit data point vector) (rotation parameter).val
    ((rotation parameter).val * generator)

theorem scalarTangent_continuous (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) : Continuous (scalarTangent data point vector) := by
  have matricesContinuous : Continuous (fun parameter : Parameter => (rotation parameter).val) :=
    Units.continuous_val.comp rotation_continuous
  have derivativesContinuous :=
    ((scalarMatrixOrbit_contDiffOn data point vector).continuousOn_fderiv_of_isOpen
      binaryDomain_isOpen (by simp)).comp_continuous matricesContinuous
        (fun parameter => Matrix.GeneralLinearGroup.det_ne_zero (rotation parameter))
  exact derivativesContinuous.clm_apply (matricesContinuous.mul continuous_const)

theorem scalarOrbit_hasDerivAt_tangent (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (time : ℝ) :
    HasDerivAt (fun time : ℝ => data.realize vector (point * atInfinity (rotation (time : Parameter))))
      (scalarTangent data point vector (time : Parameter)) time := by
  have membership : (rotation (time : Parameter)).val ∈ binaryDomain :=
    Matrix.GeneralLinearGroup.det_ne_zero _
  have regularity := ((scalarMatrixOrbit_contDiffOn data point vector) _ membership).contDiffAt
    (binaryDomain_isOpen.mem_nhds membership)
  have derivative := (regularity.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt time
    (rotation_hasDerivAt time)
  have curveEquality : scalarMatrixOrbit data point vector ∘ (fun time : ℝ => (rotation (time : Parameter)).val) =
      (fun time : ℝ => data.realize vector (point * atInfinity (rotation (time : Parameter)))) := by
    funext time
    simp only [Function.comp_apply, scalarMatrixOrbit, invertibleMatrix_units]
  rw [curveEquality] at derivative
  exact derivative

theorem smoothMode_rotationDerivative (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ) :
    smoothMode data index (rotationDerivative data vector) = frequency index • smoothMode data index vector :=
  Subtype.ext (modeVector_rotationDerivative data vector index)

/-- The actual scalar derivative agrees with realization of the Hilbert rotation derivative. -/
theorem scalarTangent_eq_realize (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) :
    scalarTangent data point vector =
      fun parameter : Parameter => data.realize (rotationDerivative data vector)
        (point * atInfinity (rotation parameter)) := by
  apply FourierUniqueness.ext _ _ (scalarTangent_continuous data point vector)
    (scalarOrbit_continuous data point (rotationDerivative data vector))
  intro index
  rw [fourierCoeff_derivative
    (fun parameter : Parameter => data.realize vector (point * atInfinity (rotation parameter)))
    _ (scalarTangent_continuous data point vector)
    (scalarOrbit_hasDerivAt_tangent data point vector)]
  change frequency index * scalarCoefficient data point index vector =
    scalarCoefficient data point index (rotationDerivative data vector)
  rw [scalarCoefficient_eq_mode, scalarCoefficient_eq_mode, smoothMode_rotationDerivative, map_smul]
  rfl

theorem scalarOrbit_hasDerivAt (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (time : ℝ) :
    HasDerivAt (fun time : ℝ => data.realize vector (point * atInfinity (rotation (time : Parameter))))
      (data.realize (rotationDerivative data vector) (point * atInfinity (rotation (time : Parameter)))) time := by
  have derivative := scalarOrbit_hasDerivAt_tangent data point vector time
  rw [scalarTangent_eq_realize] at derivative
  exact derivative

theorem scalarOrbit_sub_bound (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (first second : ℝ) :
    ‖data.realize vector (point * atInfinity (rotation (second : Parameter))) -
      data.realize vector (point * atInfinity (rotation (first : Parameter)))‖ ≤
      cuspSupNorm (rotationDerivative data vector) * |second - first| := by
  have derivativeBound (time : ℝ) :
      ‖deriv (fun time : ℝ => data.realize vector (point * atInfinity (rotation (time : Parameter)))) time‖ ≤
        cuspSupNorm (rotationDerivative data vector) := by
    rw [(scalarOrbit_hasDerivAt data point vector time).deriv]
    exact realize_le_cuspSupNorm _ _
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun time _ => (scalarOrbit_hasDerivAt data point vector time).differentiableAt)
      (fun time _ => derivativeBound time) (Set.mem_univ first) (Set.mem_univ second)

theorem cuspSupNorm_translate_sub_le (data : CuspidalRepresentation) (vector : data.smooth)
    (first second : ℝ) :
    cuspSupNorm
      ((⟨data.π (atInfinity (rotation (second : Parameter))) vector.val, data.smooth_stable _ _ vector.property⟩ :
        data.smooth) -
      (⟨data.π (atInfinity (rotation (first : Parameter))) vector.val, data.smooth_stable _ _ vector.property⟩ :
        data.smooth)) ≤ cuspSupNorm (rotationDerivative data vector) * |second - first| := by
  apply cuspSupNorm_le
  intro point
  rw [map_sub, Pi.sub_apply, data.equivariant, data.equivariant]
  exact scalarOrbit_sub_bound data point vector first second

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative
