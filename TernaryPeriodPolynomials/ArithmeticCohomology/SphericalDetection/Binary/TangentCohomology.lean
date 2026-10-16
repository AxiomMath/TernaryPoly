module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DifferentiablePotential
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRotations_smul_I (angle : Circle) :
    binaryRotations angle • UpperHalfPlane.I = UpperHalfPlane.I := by
  have positive : 0 < (Matrix.GeneralLinearGroup.det (binaryRotations angle)).val := by
    change 0 < (binaryRotationMatrix angle).det
    rw [binaryRotationMatrix_det]
    norm_num
  apply (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos positive).mpr
  constructor
  · rfl
  · simp [binaryRotations, binaryRotation]

theorem binaryReflection_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_J_smul]

theorem binaryRotations_smulFDeriv (angle : Circle) (direction : ℂ) :
    UpperHalfPlane.smulFDeriv (binaryRotations angle) Complex.I direction =
      ((angle : ℂ) ^ 2)⁻¹ * direction := by
  have determinant : (Matrix.GeneralLinearGroup.det (binaryRotations angle)).val = 1 :=
    binaryRotationMatrix_det angle
  have denominator : UpperHalfPlane.denom (binaryRotations angle) Complex.I = (angle : ℂ) := by
    apply Complex.ext <;> simp [UpperHalfPlane.denom, binaryRotations, binaryRotation]
  simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, determinant, denominator, mul_comm]

theorem binaryReflection_smulFDeriv (direction : ℂ) :
    UpperHalfPlane.smulFDeriv UpperHalfPlane.J Complex.I direction = -(starRingEnd ℂ) direction := by
  norm_num [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, UpperHalfPlane.denom, UpperHalfPlane.J]

theorem realLinear_complex_coordinates {E : Type} [AddCommGroup E] [Module ℝ E]
    (linear : ℂ →ₗ[ℝ] E) (value : ℂ) :
    linear value = value.re • linear 1 + value.im • linear Complex.I := by
  have coordinates : value.re • (1 : ℂ) + value.im • Complex.I = value := by
    apply Complex.ext <;> simp
  rw [← coordinates, map_add, map_smul, map_smul]
  simp

theorem holomorphicTangent_ne_zero {E : Type} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E]
    (linear : ℂ →ₗ[ℝ] E) (reflection : E →ₗ[ℂ] E)
    (nonzero : linear ≠ 0)
    (equivariant : ∀ value : ℂ, reflection (linear value) = linear (-(starRingEnd ℂ) value)) :
    linear 1 - Complex.I • linear Complex.I ≠ 0 := by
  intro zero
  have real_reflection : reflection (linear 1) = -linear 1 := by
    simpa only [map_one, map_neg] using equivariant 1
  have imaginary_reflection : reflection (linear Complex.I) = linear Complex.I := by
    simpa only [Complex.conj_I, neg_neg] using equivariant Complex.I
  have reflected := congrArg reflection zero
  rw [map_sub, map_smul, real_reflection, imaginary_reflection, map_zero] at reflected
  have twice_zero : (2 : ℂ) • linear 1 = 0 := by
    calc
      (2 : ℂ) • linear 1 =
          (linear 1 - Complex.I • linear Complex.I) -
            (-linear 1 - Complex.I • linear Complex.I) := by module
      _ = 0 := by rw [zero, reflected, sub_self]
  have real_zero : linear 1 = 0 := (smul_eq_zero.mp twice_zero).resolve_left (by norm_num)
  have imaginary_zero : linear Complex.I = 0 := by
    have scaled : Complex.I • linear Complex.I = 0 := by
      rw [real_zero] at zero
      exact neg_eq_zero.mp (by simpa only [zero_sub] using zero)
    exact (smul_eq_zero.mp scaled).resolve_left Complex.I_ne_zero
  apply nonzero
  ext value
  rw [realLinear_complex_coordinates, real_zero, imaginary_zero, smul_zero, smul_zero, add_zero]
  rfl

theorem holomorphicTangent_eigenvector {E : Type} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E]
    (linear : ℂ →ₗ[ℝ] E) (action : E →ₗ[ℂ] E) (eigenvalue : ℂ)
    (equivariant : ∀ value : ℂ, action (linear value) = linear (eigenvalue * value)) :
    action (linear 1 - Complex.I • linear Complex.I) =
      eigenvalue • (linear 1 - Complex.I • linear Complex.I) := by
  rw [map_sub, map_smul, equivariant, equivariant, mul_one,
    realLinear_complex_coordinates linear eigenvalue,
    realLinear_complex_coordinates linear (eigenvalue * Complex.I)]
  simp only [Complex.mul_I_re, Complex.mul_I_im]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  calc
    _ = ((eigenvalue.re : ℂ) + (eigenvalue.im : ℂ) * Complex.I) •
        (linear 1 - Complex.I • linear Complex.I) := by
      have product : ((eigenvalue.re : ℂ) + (eigenvalue.im : ℂ) * Complex.I) * Complex.I =
          (eigenvalue.re : ℂ) * Complex.I - (eigenvalue.im : ℂ) := by
        rw [add_mul, mul_assoc, Complex.I_mul_I, mul_neg_one]
        rfl
      rw [smul_sub, smul_smul, product]
      module
    _ = _ := by rw [Complex.re_add_im]

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryUpperPotential_fderiv_equivariant (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (matrix : BinaryRealGL) (point : UpperHalfPlane) :
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) ((matrix • point : UpperHalfPlane) : ℂ)).comp
        (UpperHalfPlane.smulFDeriv matrix point) =
      ((binaryHilbertOperator cusp basis matrix).restrictScalars ℝ).comp
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ)) := by
  let potential := binaryUpperPotential cusp spherical basis level cycle
  let action := (binaryHilbertOperator cusp basis matrix).restrictScalars ℝ
  let orbit : ℂ → ℂ := fun argument => (matrix • UpperHalfPlane.ofComplex argument : UpperHalfPlane)
  have orbit_value : orbit point = ((matrix • point : UpperHalfPlane) : ℂ) := by
    simp only [orbit, UpperHalfPlane.ofComplex_apply]
  have orbit_derivative : HasFDerivAt orbit (UpperHalfPlane.smulFDeriv matrix point) (point : ℂ) :=
    (UpperHalfPlane.hasStrictFDerivAt_smul matrix point).hasFDerivAt
  have target_derivative := (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (matrix • point).im_pos)).hasFDerivAt
  have at_orbit : HasFDerivAt potential
      (fderiv ℝ potential ((matrix • point : UpperHalfPlane) : ℂ)) (orbit point) :=
    orbit_value.symm ▸ target_derivative
  have left_derivative := at_orbit.comp (point : ℂ) orbit_derivative
  have source_derivative := (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos)).hasFDerivAt
  have right_derivative := (action.hasFDerivAt.comp (point : ℂ) source_derivative).const_add
    (cycle matrix : binaryHilbertFiniteValues cusp level).val
  have equality : potential ∘ orbit =ᶠ[nhds (point : ℂ)]
      (fun argument => (cycle matrix : binaryHilbertFiniteValues cusp level).val + action (potential argument)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos] with argument member
    have realization := congrArg Subtype.val (binarySymmetricPotential_affine _ cycle stabilizer_zero
      matrix (⟨argument, member⟩ : UpperHalfPlane))
    change (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle
      (matrix • (⟨argument, member⟩ : UpperHalfPlane)) : binaryHilbertFiniteValues cusp level).val =
        (cycle matrix : binaryHilbertFiniteValues cusp level).val +
          binaryHilbertOperator cusp basis matrix
            (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle
              (⟨argument, member⟩ : UpperHalfPlane) : binaryHilbertFiniteValues cusp level).val at realization
    rw [← binaryUpperPotential_coe, ← binaryUpperPotential_coe] at realization
    change potential (orbit argument) =
      (cycle matrix : binaryHilbertFiniteValues cusp level).val + action (potential argument)
    dsimp only [orbit]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos member]
    exact realization
  exact left_derivative.unique (right_derivative.congr_of_eventuallyEq equality)

theorem binaryUpperPotential_fderiv_rotation (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (angle : Circle) (direction : ℂ) :
    binaryHilbertOperator cusp basis (binaryRotations angle)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) =
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
          (((angle : ℂ) ^ 2)⁻¹ * direction) := by
  have equivariant := binaryUpperPotential_fderiv_equivariant cusp spherical basis level cycle regular
    stabilizer_zero (binaryRotations angle) UpperHalfPlane.I
  rw [binaryRotations_smul_I] at equivariant
  have evaluated := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction) equivariant
  change fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
      (UpperHalfPlane.smulFDeriv (binaryRotations angle) Complex.I direction) =
    binaryHilbertOperator cusp basis (binaryRotations angle)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) at evaluated
  rw [binaryRotations_smulFDeriv] at evaluated
  exact evaluated.symm

theorem binaryUpperPotential_fderiv_reflection (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (direction : ℂ) :
    binaryHilbertOperator cusp basis UpperHalfPlane.J
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) =
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
          (-(starRingEnd ℂ) direction) := by
  have equivariant := binaryUpperPotential_fderiv_equivariant cusp spherical basis level cycle regular
    stabilizer_zero UpperHalfPlane.J UpperHalfPlane.I
  rw [binaryReflection_smul_I] at equivariant
  have evaluated := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction) equivariant
  change fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
      (UpperHalfPlane.smulFDeriv UpperHalfPlane.J Complex.I direction) =
    binaryHilbertOperator cusp basis UpperHalfPlane.J
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) at evaluated
  rw [binaryReflection_smulFDeriv] at evaluated
  exact evaluated.symm

def binaryHolomorphicTangent (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) : index → cusp.H :=
  fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 -
    Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I

theorem binaryHolomorphicTangent_nonzero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    binaryHolomorphicTangent cusp spherical basis level cycle ≠ 0 := by
  apply holomorphicTangent_ne_zero
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I).toLinearMap
    (binaryHilbertOperator cusp basis UpperHalfPlane.J).toLinearMap
  · intro zero
    apply binaryUpperPotential_fderiv_basepoint_ne_zero cusp spherical basis level cycle nonzero regular stabilizer_zero
    apply ContinuousLinearMap.ext
    intro value
    exact LinearMap.congr_fun zero value
  · exact binaryUpperPotential_fderiv_reflection cusp spherical basis level cycle regular stabilizer_zero

theorem binaryHolomorphicTangent_rotation (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (angle : Circle) :
    binaryHilbertOperator cusp basis (binaryRotations angle)
      (binaryHolomorphicTangent cusp spherical basis level cycle) =
        ((angle : ℂ) ^ 2)⁻¹ • binaryHolomorphicTangent cusp spherical basis level cycle :=
  holomorphicTangent_eigenvector
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I).toLinearMap
    (binaryHilbertOperator cusp basis (binaryRotations angle)).toLinearMap _
    (binaryUpperPotential_fderiv_rotation cusp spherical basis level cycle regular stabilizer_zero angle)

theorem binaryUpperPotential_fderiv_finiteLevel (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (element : level) (direction : ℂ) (position : index) :
    cusp.π (atFinite element.val)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction position) =
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction position := by
  let potential := binaryUpperPotential cusp spherical basis level cycle
  let action := (binaryHilbertTranslation (index := index) cusp (atFinite element.val)).restrictScalars ℝ
  have fixed (argument : ℂ) : action (potential argument) = potential argument := by
    funext coordinate
    exact (cycle (invertibleMatrix (binaryUpperSectionMatrix argument)) :
      binaryHilbertFiniteValues cusp level).property element coordinate
  have derivative := (regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp))).hasFDerivAt
  have composed := action.hasFDerivAt.comp Complex.I derivative
  have same := (composed.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun argument => (fixed argument).symm))).unique derivative
  have evaluated := congrArg (fun map : ℂ →L[ℝ] (index → cusp.H) => map direction position) same
  exact evaluated

theorem binaryHolomorphicTangent_finiteLevel (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (element : level) (position : index) :
    cusp.π (atFinite element.val) (binaryHolomorphicTangent cusp spherical basis level cycle position) =
      binaryHolomorphicTangent cusp spherical basis level cycle position := by
  simp only [binaryHolomorphicTangent, Pi.sub_apply, Pi.smul_apply, map_sub, map_smul,
    binaryUpperPotential_fderiv_finiteLevel cusp spherical basis level cycle regular element]

theorem cohomological_exists_rotation_eigenvector (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL) (vector : index → cusp.H),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧ vector ≠ 0 ∧
      (∀ element : level, ∀ position, cusp.π (atFinite element.val) (vector position) = vector position) ∧
      ∀ angle : Circle, binaryHilbertOperator cusp basis (binaryRotations angle) vector =
        ((angle : ℂ) ^ 2)⁻¹ • vector := by
  obtain ⟨level, cycle, level_open, level_compact, nonzero, regular, stabilizer_zero, _⟩ :=
    cohomological_exists_symmetric_basepoint_differential cusp spherical cohomological basis
  have differentiable := regular.differentiableOn (by simp)
  exact ⟨level, binaryHolomorphicTangent cusp spherical basis level cycle, level_open, level_compact,
    binaryHolomorphicTangent_nonzero cusp spherical basis level cycle nonzero differentiable stabilizer_zero,
    binaryHolomorphicTangent_finiteLevel cusp spherical basis level cycle differentiable,
    binaryHolomorphicTangent_rotation cusp spherical basis level cycle differentiable stabilizer_zero⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
