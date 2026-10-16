module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ExtremalSpherical
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderDecomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryComplexReflection : ℂ →L[ℝ] ℂ := -Complex.conjCLE.toContinuousLinearMap

theorem binaryComplexReflection_im (point : ℂ) : (binaryComplexReflection point).im = point.im := by
  simp [binaryComplexReflection]

theorem binaryComplexReflection_basepoint : binaryComplexReflection Complex.I = Complex.I := by
  simp [binaryComplexReflection]

theorem binarySymmetricSection_mul_reflection (point : UpperHalfPlane) :
    binarySymmetricSection point * UpperHalfPlane.J =
      UpperHalfPlane.J * binarySymmetricSection
        ⟨binaryComplexReflection point, by rw [binaryComplexReflection_im]; exact point.im_pos⟩ := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binarySymmetricSection, UpperHalfPlane.toSL2R, UpperHalfPlane.J,
      binaryComplexReflection, SpecialLinearGroup.toGL, Matrix.mul_apply, Fin.sum_univ_two, neg_div]

theorem cuspAffineOrbitVector_reflection (cusp : CuspidalRepresentation) (vector : cusp.H)
    (point : ℂ) (positive : 0 < point.im) :
    cuspAffineOrbitVector cusp (cusp.π (atInfinity UpperHalfPlane.J) vector) point =
      cusp.π (atInfinity UpperHalfPlane.J)
        (cuspAffineOrbitVector cusp vector (binaryComplexReflection point)) := by
  let upper : UpperHalfPlane := ⟨point, positive⟩
  let reflected : UpperHalfPlane :=
    ⟨binaryComplexReflection point, by simpa only [binaryComplexReflection_im] using positive⟩
  rw [cuspAffineOrbitVector, binaryUpperSectionMatrix_coe upper, invertibleMatrix_coe,
    cuspAffineOrbitVector, binaryUpperSectionMatrix_coe reflected, invertibleMatrix_coe]
  change (cusp.π (atInfinity (binarySymmetricSection upper)) * cusp.π (atInfinity UpperHalfPlane.J)) vector =
    (cusp.π (atInfinity UpperHalfPlane.J) * cusp.π (atInfinity (binarySymmetricSection reflected))) vector
  rw [← map_mul, ← map_mul, ← atInfinity_mul, ← atInfinity_mul,
    binarySymmetricSection_mul_reflection]

theorem cuspAffineOrbitVector_reflection_contDiffOn (cusp : CuspidalRepresentation) (vector : cusp.H)
    {order : WithTop ℕ∞}
    (regular : ContDiffOn ℝ order (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ order (cuspAffineOrbitVector cusp (cusp.π (atInfinity UpperHalfPlane.J) vector))
      UpperHalfPlane.upperHalfPlaneSet := by
  have reflected := regular.comp binaryComplexReflection.contDiff.contDiffOn
    (show Set.MapsTo binaryComplexReflection UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet from
      fun point positive => by change 0 < (binaryComplexReflection point).im; rw [binaryComplexReflection_im]; exact positive)
  apply ((cuspUnitaryOperator cusp (atInfinity UpperHalfPlane.J)).restrictScalars ℝ).contDiff.comp_contDiffOn reflected |>.congr
  intro point positive
  exact cuspAffineOrbitVector_reflection cusp vector point positive

theorem cuspAffineOrbitVector_reflection_fderiv (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) (direction : ℂ) :
    fderiv ℝ (cuspAffineOrbitVector cusp (cusp.π (atInfinity UpperHalfPlane.J) vector)) Complex.I direction =
      cusp.π (atInfinity UpperHalfPlane.J)
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I (binaryComplexReflection direction)) := by
  have at_reflected : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) (binaryComplexReflection Complex.I) :=
    binaryComplexReflection_basepoint.symm ▸ regular
  have derivative := ((cuspUnitaryOperator cusp (atInfinity UpperHalfPlane.J)).restrictScalars ℝ).hasFDerivAt.comp Complex.I
    (at_reflected.hasFDerivAt.comp Complex.I binaryComplexReflection.hasFDerivAt)
  have equality : cuspAffineOrbitVector cusp (cusp.π (atInfinity UpperHalfPlane.J) vector) =ᶠ[nhds Complex.I]
      (fun point => cusp.π (atInfinity UpperHalfPlane.J) (cuspAffineOrbitVector cusp vector (binaryComplexReflection point))) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp)] with point positive
    exact cuspAffineOrbitVector_reflection cusp vector point positive
  rw [(derivative.congr_of_eventuallyEq equality).fderiv]
  simp only [ContinuousLinearMap.comp_apply, binaryComplexReflection_basepoint]
  rfl

theorem cuspRaisingVector_reflection (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    cuspRaisingVector cusp (-weight) (cusp.π (atInfinity UpperHalfPlane.J) vector) =
      -cusp.π (atInfinity UpperHalfPlane.J) (cuspLoweringVector cusp weight vector) := by
  simp only [cuspRaisingVector, cuspLoweringVector,
    cuspAffineOrbitVector_reflection_fderiv cusp vector regular,
    binaryComplexReflection_basepoint, Int.cast_neg, map_add, map_sub, map_smul]
  have horizontal : binaryComplexReflection 1 = -1 := by simp [binaryComplexReflection]
  rw [horizontal, map_neg, map_neg]
  module

theorem cuspReflection_rotation (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (cusp.π (atInfinity UpperHalfPlane.J) vector) =
      (angle : ℂ) ^ (-weight) • cusp.π (atInfinity UpperHalfPlane.J) vector := by
  change (cusp.π (atInfinity (binaryRotations angle)) * cusp.π (atInfinity UpperHalfPlane.J)) vector = _
  rw [← map_mul, ← atInfinity_mul, binaryRotation_mul_reflection, atInfinity_mul,
    map_mul, Module.End.mul_apply, rotation, map_smul, Circle.coe_inv, inv_zpow, zpow_neg]

theorem cuspReflection_finiteLevel (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : cusp.H) (fixed : ∀ element : level, cusp.π (atFinite element.val) vector = vector)
    (element : level) :
    cusp.π (atFinite element.val) (cusp.π (atInfinity UpperHalfPlane.J) vector) =
      cusp.π (atInfinity UpperHalfPlane.J) vector := by
  change (cusp.π (atFinite element.val) * cusp.π (atInfinity UpperHalfPlane.J)) vector = _
  rw [← map_mul, (atInfinity_commute_atFinite UpperHalfPlane.J element.val).symm.eq,
    map_mul, Module.End.mul_apply, fixed]

theorem cuspReflection_weightValues (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (vector : cusp.H) (member : vector ∈ cuspHilbertWeightValues cusp level weight) :
    cusp.π (atInfinity UpperHalfPlane.J) vector ∈ cuspHilbertWeightValues cusp level (-weight) :=
  ⟨cuspReflection_finiteLevel cusp level vector member.1, cuspReflection_rotation cusp weight vector member.2⟩

theorem cusp_exists_spherical_smooth_of_lowering_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (halfWeight : ℤ) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ (2 * halfWeight) • vector)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (lowering_zero : cuspLoweringVector cusp (2 * halfWeight) vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ cuspSphericalValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * (-halfWeight)) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp (-halfWeight) spherical_vector.val) UpperHalfPlane.upperHalfPlaneSet := by
  have reflected_nonzero : cusp.π (atInfinity UpperHalfPlane.J) vector ≠ 0 := by
    exact (map_ne_zero_iff (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J))
      (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J)).injective).mpr nonzero
  have reflected_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) (cusp.π (atInfinity UpperHalfPlane.J) vector) =
        (angle : ℂ) ^ (2 * (-halfWeight)) • cusp.π (atInfinity UpperHalfPlane.J) vector := by
    simpa only [mul_neg] using cuspReflection_rotation cusp (2 * halfWeight) vector rotation
  have reflected_regular := cuspAffineOrbitVector_reflection_contDiffOn cusp vector regular
  have reflected_zero : cuspRaisingVector cusp (2 * (-halfWeight)) (cusp.π (atInfinity UpperHalfPlane.J) vector) = 0 := by
    rw [mul_neg, cuspRaisingVector_reflection cusp (2 * halfWeight) vector
      ((regular.differentiableOn (by simp)).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp))), lowering_zero, map_zero, neg_zero]
  exact cusp_exists_spherical_smooth_raising_zero cusp spherical central_positive
    (cusp.π (atInfinity UpperHalfPlane.J) vector) (-halfWeight) reflected_nonzero
    reflected_rotation reflected_regular reflected_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
