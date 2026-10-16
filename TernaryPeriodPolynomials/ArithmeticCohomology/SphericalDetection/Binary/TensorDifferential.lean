module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineCoefficientDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryAffineSection_normalizingFactor (point : ℂ) (positive : 0 < point.im) (exponent : ℂ) :
    normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point)))) exponent = 1 := by
  rw [binary_normalizingFactor_eq, invertibleMatrix_val _ (binaryUpperSectionMatrix_invertible point positive),
    binaryUpperSectionMatrix_det point positive, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem complexAffineLine_hasDerivAt (direction : ℂ) :
    HasDerivAt (fun parameter : ℝ => Complex.I + parameter • direction) direction 0 := by
  convert ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add Complex.I using 1
  · rfl
  · exact (one_smul ℝ direction).symm

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryAffineOrbitVector_fderiv (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : index → cusp.H)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis vector) UpperHalfPlane.upperHalfPlaneSet)
    (direction : ℂ) :
    fderiv ℝ (binaryAffineOrbitVector cusp basis vector) Complex.I direction =
      finiteTensorOperator basis (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative direction)) vector +
        fun position => fderiv ℝ (cuspAffineOrbitVector cusp (vector position)) Complex.I direction := by
  classical
  have neighborhood : UpperHalfPlane.upperHalfPlaneSet ∈ nhds Complex.I :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simp)
  have line_derivative := complexAffineLine_hasDerivAt direction
  have tensor_derivative := ((regular.contDiffAt neighborhood).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 line_derivative (by simp)
  have unitary_derivative (position : index) :
      HasDerivAt (fun parameter : ℝ => cuspAffineOrbitVector cusp (vector position) (Complex.I + parameter • direction))
        (fderiv ℝ (cuspAffineOrbitVector cusp (vector position)) Complex.I direction) 0 := by
    have coordinate_regular := cuspAffineOrbitVector_coordinate_contDiffOn cusp basis vector regular position
    exact ((coordinate_regular.contDiffAt neighborhood).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 line_derivative (by simp)
  funext position
  have sum_derivative := HasDerivAt.sum (u := Finset.univ) (fun source (_ : source ∈ Finset.univ) =>
    (binaryAffineCoefficient_functional_hasDerivAt direction (basis source) (basis.coord position)).smul
      (unitary_derivative source))
  have derivative_value :
      (∑ source, (basis.coord position (binaryCoefficient degree
          (invertibleMatrix (binaryUpperSectionMatrix (Complex.I + (0 : ℝ) • direction))) (basis source)) •
          fderiv ℝ (cuspAffineOrbitVector cusp (vector source)) Complex.I direction +
        basis.coord position
          (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative direction) (basis source)) •
          cuspAffineOrbitVector cusp (vector source) (Complex.I + (0 : ℝ) • direction))) =
      finiteTensorOperator basis (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative direction)) vector position +
        fderiv ℝ (cuspAffineOrbitVector cusp (vector position)) Complex.I direction := by
    simp only [zero_smul, add_zero, cuspAffineOrbitVector_I, binaryAffineSection_I,
      binaryCoefficient, map_one, Module.End.one_apply, Finset.sum_add_distrib, finiteTensorOperator_apply]
    rw [add_comm]
    congr 1
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  rw [derivative_value] at sum_derivative
  have actual_derivative := ((ContinuousLinearMap.proj position : (index → cusp.H) →L[ℂ] cusp.H).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 tensor_derivative
  apply actual_derivative.unique
  apply sum_derivative.congr_of_eventuallyEq
  filter_upwards [binaryAffineLine_eventually_positive direction] with parameter positive
  change binaryAffineOrbitVector cusp basis vector (Complex.I + parameter • direction) position = _
  simp only [Finset.sum_apply, Pi.smul_apply', binaryAffineOrbitVector, binaryHilbertOperator_apply,
    binaryAffineSection_normalizingFactor _ positive, one_smul, cuspAffineOrbitVector]

/-- The actual relative equation after separating the polynomial and unitary derivatives. -/
theorem binaryRelativeCocycle_unitary_equation (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (first second : index → cusp.H)
    (first_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis first) UpperHalfPlane.upperHalfPlaneSet)
    (second_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis second) UpperHalfPlane.upperHalfPlaneSet)
    (relative : fderiv ℝ (binaryAffineOrbitVector cusp basis first) Complex.I Complex.I -
      fderiv ℝ (binaryAffineOrbitVector cusp basis second) Complex.I 1 = first)
    (position : index) :
    fderiv ℝ (cuspAffineOrbitVector cusp (first position)) Complex.I Complex.I -
      fderiv ℝ (cuspAffineOrbitVector cusp (second position)) Complex.I 1 =
        first position -
          finiteTensorOperator basis (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative Complex.I)) first position +
          finiteTensorOperator basis (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative 1)) second position := by
  rw [binaryAffineOrbitVector_fderiv cusp basis first first_regular,
    binaryAffineOrbitVector_fderiv cusp basis second second_regular] at relative
  have coordinate := congrFun relative position
  change _ + fderiv ℝ (cuspAffineOrbitVector cusp (first position)) Complex.I Complex.I -
    (_ + fderiv ℝ (cuspAffineOrbitVector cusp (second position)) Complex.I 1) = first position at coordinate
  conv_rhs => rw [← coordinate]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
