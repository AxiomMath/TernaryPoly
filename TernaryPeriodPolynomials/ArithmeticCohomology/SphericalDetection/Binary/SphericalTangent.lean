module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalWeights
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.InfinitesimalUnitarity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

def binarySphericalTranslateOperator (cusp : CuspidalRepresentation) (finite : BinaryFiniteGL) :
    (index → cusp.H) →L[ℂ] (index → cusp.H) :=
  ContinuousLinearMap.piMap (fun _ =>
    (cuspSphericalProjection cusp).comp (cuspUnitaryOperator cusp (atFinite finite)))

omit [Fintype index] in
theorem binarySphericalTranslateOperator_apply (cusp : CuspidalRepresentation)
    (finite : BinaryFiniteGL) (vector : index → cusp.H) (position : index) :
    binarySphericalTranslateOperator cusp finite vector position =
      cuspSphericalProjection cusp (cusp.π (atFinite finite) (vector position)) := rfl

omit [Fintype index] in
theorem binarySphericalTranslateOperator_mem (cusp : CuspidalRepresentation)
    (finite : BinaryFiniteGL) (vector : index → cusp.H) (position : index) :
    binarySphericalTranslateOperator cusp finite vector position ∈ cuspSphericalValues cusp :=
  cuspSphericalProjection_mem cusp _

theorem binarySphericalTranslateOperator_real (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (finite : BinaryFiniteGL) (real : BinaryRealGL) (vector : index → cusp.H) :
    binarySphericalTranslateOperator cusp finite (binaryHilbertOperator cusp basis real vector) =
      binaryHilbertOperator cusp basis real (binarySphericalTranslateOperator cusp finite vector) := by
  funext position
  simp only [binarySphericalTranslateOperator_apply, binaryHilbertOperator_apply, map_smul, map_sum,
    cuspSphericalProjection_finite_real]

omit [Fintype index] in
theorem binarySphericalTranslateOperator_exists_nonzero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (vector : index → cusp.H) (nonzero : vector ≠ 0) :
    ∃ finite : BinaryFiniteGL, binarySphericalTranslateOperator cusp finite vector ≠ 0 := by
  obtain ⟨position, coordinate_nonzero⟩ := Function.ne_iff.mp nonzero
  obtain ⟨finite, projected_nonzero⟩ :=
    cuspSphericalProjection_finite_nonzero cusp spherical (vector position) coordinate_nonzero
  exact ⟨finite, fun zero => projected_nonzero (congrFun zero position)⟩

theorem binarySphericalTranslateOperator_affine (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (finite : BinaryFiniteGL) (vector : index → cusp.H) :
    binaryAffineOrbitVector cusp basis (binarySphericalTranslateOperator cusp finite vector) =
      fun point => binarySphericalTranslateOperator cusp finite (binaryAffineOrbitVector cusp basis vector point) := by
  funext point
  exact (binarySphericalTranslateOperator_real cusp basis finite _ vector).symm

theorem binarySphericalTranslateOperator_affine_contDiffOn (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (finite : BinaryFiniteGL) (vector : index → cusp.H) {order : WithTop ℕ∞}
    (regular : ContDiffOn ℝ order (binaryAffineOrbitVector cusp basis vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ order
      (binaryAffineOrbitVector cusp basis (binarySphericalTranslateOperator cusp finite vector))
      UpperHalfPlane.upperHalfPlaneSet := by
  rw [binarySphericalTranslateOperator_affine]
  exact (binarySphericalTranslateOperator cusp finite).restrictScalars ℝ |>.contDiff.comp_contDiffOn regular

theorem binarySphericalTranslateOperator_affine_fderiv (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (finite : BinaryFiniteGL) (vector : index → cusp.H)
    (regular : DifferentiableAt ℝ (binaryAffineOrbitVector cusp basis vector) Complex.I)
    (direction : ℂ) :
    fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySphericalTranslateOperator cusp finite vector))
      Complex.I direction =
      binarySphericalTranslateOperator cusp finite
        (fderiv ℝ (binaryAffineOrbitVector cusp basis vector) Complex.I direction) := by
  rw [binarySphericalTranslateOperator_affine]
  exact congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction)
    (((binarySphericalTranslateOperator cusp finite).restrictScalars ℝ).hasFDerivAt.comp
      Complex.I regular.hasFDerivAt).fderiv

theorem cohomological_exists_spherical_relative_tangent (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ first second : index → cusp.H,
      first - Complex.I • second ≠ 0 ∧
      (∀ position, first position ∈ cuspSphericalValues cusp ∧ second position ∈ cuspSphericalValues cusp) ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis first) UpperHalfPlane.upperHalfPlaneSet ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis second) UpperHalfPlane.upperHalfPlaneSet ∧
      (∀ angle : Circle, binaryHilbertOperator cusp basis (binaryRotations angle) (first - Complex.I • second) =
        ((angle : ℂ) ^ 2)⁻¹ • (first - Complex.I • second)) ∧
      fderiv ℝ (binaryAffineOrbitVector cusp basis first) Complex.I Complex.I -
        fderiv ℝ (binaryAffineOrbitVector cusp basis second) Complex.I 1 = first := by
  obtain ⟨level, cycle, _, _, nonzero, regular, stabilizer_zero, _⟩ :=
    cohomological_exists_symmetric_basepoint_differential cusp spherical cohomological basis
  let first := fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1
  let second := fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I
  have tangent_nonzero : first - Complex.I • second ≠ 0 :=
    binaryHolomorphicTangent_nonzero cusp spherical basis level cycle nonzero
      (regular.differentiableOn (by simp)) stabilizer_zero
  obtain ⟨finite, projected_nonzero⟩ :=
    binarySphericalTranslateOperator_exists_nonzero cusp spherical (first - Complex.I • second) tangent_nonzero
  let operator := binarySphericalTranslateOperator (index := index) cusp finite
  have first_regular := binaryAffineOrbitVector_tangent_contDiffOn cusp spherical basis level cycle regular
    stabilizer_zero 1
  have second_regular := binaryAffineOrbitVector_tangent_contDiffOn cusp spherical basis level cycle regular
    stabilizer_zero Complex.I
  refine ⟨operator first, operator second, ?_, ?_,
    binarySphericalTranslateOperator_affine_contDiffOn cusp basis finite first first_regular,
    binarySphericalTranslateOperator_affine_contDiffOn cusp basis finite second second_regular, ?_, ?_⟩
  · simpa only [map_sub, map_smul] using projected_nonzero
  · intro position
    exact ⟨binarySphericalTranslateOperator_mem cusp finite first position,
      binarySphericalTranslateOperator_mem cusp finite second position⟩
  · intro angle
    have rotation := binaryHolomorphicTangent_rotation cusp spherical basis level cycle
      (regular.differentiableOn (by simp)) stabilizer_zero angle
    change binaryHilbertOperator cusp basis (binaryRotations angle) (first - Complex.I • second) =
      ((angle : ℂ) ^ 2)⁻¹ • (first - Complex.I • second) at rotation
    change binaryHilbertOperator cusp basis (binaryRotations angle) (operator first - Complex.I • operator second) = _
    rw [← map_smul, ← map_sub]
    rw [← binarySphericalTranslateOperator_real, rotation, map_smul]
  · have neighborhood : UpperHalfPlane.upperHalfPlaneSet ∈ nhds Complex.I :=
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simp)
    have first_differentiable := (first_regular.contDiffAt neighborhood).differentiableAt (by simp)
    have second_differentiable := (second_regular.contDiffAt neighborhood).differentiableAt (by simp)
    rw [binarySphericalTranslateOperator_affine_fderiv cusp basis finite first first_differentiable,
      binarySphericalTranslateOperator_affine_fderiv cusp basis finite second second_differentiable, ← map_sub]
    exact congrArg operator
      (binaryTangent_relativeCocycle cusp spherical basis level cycle regular stabilizer_zero)

theorem cohomological_exists_spherical_regular_rotation_weight (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree) :
    ∃ (vector : cusp.H) (weight : ℤ), vector ≠ 0 ∧ vector ∈ cuspSphericalValues cusp ∧
      (-(degree : ℤ) - 3 ≤ weight ∧ weight ≤ (degree : ℤ) - 1) ∧
      (Odd degree → Even weight) ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet ∧
      ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
        (angle : ℂ) ^ weight • vector := by
  obtain ⟨first, second, nonzero, fixed, first_regular, second_regular, rotation, _⟩ :=
    cohomological_exists_spherical_relative_tangent cusp spherical cohomological (binaryRotationBasis (degree + 1))
  obtain ⟨position, coordinate_nonzero⟩ := Function.ne_iff.mp nonzero
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryAffineOrbitVector cusp (binaryRotationBasis (degree + 1)) (first - Complex.I • second))
      UpperHalfPlane.upperHalfPlaneSet := by
    apply (first_regular.sub (second_regular.const_smul Complex.I)).congr
    intro point _
    simp only [binaryAffineOrbitVector, map_sub, map_smul]
  refine ⟨(first - Complex.I • second) position, binaryCuspRotationWeight position, coordinate_nonzero,
    ?_, binaryCuspRotationWeight_bounds position, fun odd => binaryCuspRotationWeight_even odd position,
    cuspAffineOrbitVector_coordinate_contDiffOn cusp (binaryRotationBasis (degree + 1)) _ regular position,
    binaryRotation_eigenvector_coordinate cusp _ rotation position⟩
  exact (cuspSphericalValues cusp).sub_mem (fixed position).1
    ((cuspSphericalValues cusp).smul_mem Complex.I (fixed position).2)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
