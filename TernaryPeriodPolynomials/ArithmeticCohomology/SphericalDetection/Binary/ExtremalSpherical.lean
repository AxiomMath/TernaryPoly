module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalWeights

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspAffineOrbitVector_intertwiner (cusp : CuspidalRepresentation) (operator : cusp.H →L[ℂ] cusp.H)
    (commutes : ∀ matrix vector, operator (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (operator vector)) (vector : cusp.H) :
    cuspAffineOrbitVector cusp (operator vector) = fun point => operator (cuspAffineOrbitVector cusp vector point) := by
  funext point
  exact (commutes _ vector).symm

theorem cuspAffineOrbitVector_intertwiner_contDiffOn (cusp : CuspidalRepresentation) (operator : cusp.H →L[ℂ] cusp.H)
    (commutes : ∀ matrix vector, operator (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (operator vector)) (vector : cusp.H) {order : WithTop ℕ∞}
    (regular : ContDiffOn ℝ order (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ order (cuspAffineOrbitVector cusp (operator vector)) UpperHalfPlane.upperHalfPlaneSet := by
  rw [cuspAffineOrbitVector_intertwiner cusp operator commutes]
  exact (operator.restrictScalars ℝ).contDiff.comp_contDiffOn regular

theorem cuspAffineOrbitVector_intertwiner_fderiv (cusp : CuspidalRepresentation) (operator : cusp.H →L[ℂ] cusp.H)
    (commutes : ∀ matrix vector, operator (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (operator vector)) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) (direction : ℂ) :
    fderiv ℝ (cuspAffineOrbitVector cusp (operator vector)) Complex.I direction =
      operator (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction) := by
  rw [cuspAffineOrbitVector_intertwiner cusp operator commutes]
  exact congrArg (fun derivative : ℂ →L[ℝ] cusp.H => derivative direction)
    (((operator.restrictScalars ℝ).hasFDerivAt.comp Complex.I regular.hasFDerivAt).fderiv)

theorem cuspRaisingVector_intertwiner (cusp : CuspidalRepresentation) (operator : cusp.H →L[ℂ] cusp.H)
    (commutes : ∀ matrix vector, operator (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (operator vector)) (weight : ℤ) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    cuspRaisingVector cusp weight (operator vector) = operator (cuspRaisingVector cusp weight vector) := by
  simp only [cuspRaisingVector, cuspAffineOrbitVector_intertwiner_fderiv cusp operator commutes vector regular,
    map_add, map_smul]

theorem cuspLoweringVector_intertwiner (cusp : CuspidalRepresentation) (operator : cusp.H →L[ℂ] cusp.H)
    (commutes : ∀ matrix vector, operator (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (operator vector)) (weight : ℤ) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    cuspLoweringVector cusp weight (operator vector) = operator (cuspLoweringVector cusp weight vector) := by
  simp only [cuspLoweringVector, cuspAffineOrbitVector_intertwiner_fderiv cusp operator commutes vector regular,
    map_add, map_sub, map_smul]

theorem cusp_exists_spherical_smooth_raising_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (halfWeight : ℤ) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ (2 * halfWeight) • vector)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ cuspSphericalValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * halfWeight) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * halfWeight) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight spherical_vector.val) UpperHalfPlane.upperHalfPlaneSet := by
  obtain ⟨finite, detected⟩ := cuspSphericalProjection_finite_nonzero cusp spherical vector nonzero
  let operator := (cuspSphericalProjection cusp).comp (cuspUnitaryOperator cusp (atFinite finite))
  have commutes : ∀ matrix value, operator (cusp.π (atInfinity matrix) value) =
      cusp.π (atInfinity matrix) (operator value) := cuspSphericalProjection_finite_real cusp finite
  have projected_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) (operator vector) =
        (angle : ℂ) ^ (2 * halfWeight) • operator vector := by
    intro angle
    rw [← commutes, rotation, map_smul]
  have projected_fixed : operator vector ∈ cuspSphericalValues cusp := cuspSphericalProjection_mem cusp _
  have projected_regular := cuspAffineOrbitVector_intertwiner_contDiffOn cusp operator commutes vector regular
  have differentiable := (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I.im > 0 by simp))).differentiableAt (by simp)
  have projected_zero : cuspRaisingVector cusp (2 * halfWeight) (operator vector) = 0 := by
    rw [cuspRaisingVector_intertwiner cusp operator commutes _ vector differentiable, raising_zero, map_zero]
  have projected_differentiable := projected_regular.differentiableOn (by simp)
  have smooth := cuspSphericalWeight_smooth_of_raising_zero cusp spherical central_positive
    (operator vector) halfWeight projected_rotation projected_fixed projected_differentiable projected_zero
  refine ⟨⟨operator vector, smooth⟩, ?_, projected_fixed, projected_rotation, projected_zero, ?_⟩
  · intro zero
    exact detected (congrArg Subtype.val zero)
  · exact cuspWeightedAffineOrbit_holomorphic cusp halfWeight (operator vector) projected_differentiable projected_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
