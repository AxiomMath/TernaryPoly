module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineDerivatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryCocycle_H1_zero_of_positive_zero (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (positive_zero : ∀ matrix : BinaryRealGL, 0 < (GeneralLinearGroup.det matrix).val → cycle matrix = 0) :
    groupCohomology.H1π representation cycle = 0 := by
  let primitive : representation := -(2 : ℂ)⁻¹ • cycle UpperHalfPlane.J
  let shifted := shiftCocycle representation cycle primitive
  have reflection_zero : shifted UpperHalfPlane.J = 0 :=
    shiftCocycle_involution representation cycle _ (by simpa only [pow_two] using UpperHalfPlane.J_sq)
  have shifted_positive (matrix : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det matrix).val) : shifted matrix = 0 := by
    apply shiftCocycle_zero_of_fixed representation cycle primitive matrix (positive_zero matrix positive)
    have conjugate_positive : 0 < (GeneralLinearGroup.det (UpperHalfPlane.J * matrix * UpperHalfPlane.J)).val := by
      simpa only [map_mul, Units.val_mul, UpperHalfPlane.det_J, Units.val_neg, Units.val_one,
        neg_one_mul, mul_neg_one, neg_neg] using positive
    have commutation : matrix * UpperHalfPlane.J = UpperHalfPlane.J * (UpperHalfPlane.J * matrix * UpperHalfPlane.J) := by
      rw [← mul_assoc UpperHalfPlane.J, ← mul_assoc UpperHalfPlane.J, ← pow_two, UpperHalfPlane.J_sq, one_mul]
    change representation.ρ matrix (-(2 : ℂ)⁻¹ • cycle UpperHalfPlane.J) = _
    rw [map_smul, cocycle_normalizer_fixed representation cycle matrix UpperHalfPlane.J
      (UpperHalfPlane.J * matrix * UpperHalfPlane.J) commutation (positive_zero matrix positive)
      (positive_zero _ conjugate_positive)]
  have shifted_zero : shifted = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    rcases lt_or_gt_of_ne (GeneralLinearGroup.det matrix).ne_zero with negative | positive
    · have product_positive : 0 < (GeneralLinearGroup.det (matrix * UpperHalfPlane.J)).val := by
        simpa only [map_mul, Units.val_mul, UpperHalfPlane.det_J, Units.val_neg, Units.val_one,
          mul_neg_one, neg_pos] using negative
      exact (cocycle_right_eq_of_zero representation shifted matrix UpperHalfPlane.J reflection_zero).symm.trans
        (shifted_positive _ product_positive)
    · exact shifted_positive matrix positive
  have zero : groupCohomology.H1π representation shifted = 0 := by rw [shifted_zero, map_zero]
  exact (shiftCocycle_H1 representation cycle primitive).symm.trans zero

theorem binaryCocycle_positive_zero_of_sections (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (sections_zero : ∀ point : UpperHalfPlane, cycle (binarySymmetricSection point) = 0)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (central_zero : ∀ unit : ℝˣ, 0 < unit.val → cycle (GeneralLinearGroup.scalar (Fin 2) unit) = 0)
    (matrix : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det matrix).val) : cycle matrix = 0 := by
  let lift := binarySymmetricSection (matrix • UpperHalfPlane.I)
  have lift_det : (GeneralLinearGroup.det lift).val = 1 :=
    (matrix • UpperHalfPlane.I).toSL2R.property
  have fixes : (lift⁻¹ * matrix) • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [mul_smul, ← binarySymmetricSection_smul (matrix • UpperHalfPlane.I)]
    exact inv_smul_smul lift UpperHalfPlane.I
  have positive_stabilizer : 0 < (GeneralLinearGroup.det (lift⁻¹ * matrix)).val := by
    simpa only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, lift_det, inv_one, one_mul] using positive
  obtain ⟨unit, angle, unit_positive, decomposition⟩ :=
    binary_stabilizer_positive_decomposition (lift⁻¹ * matrix) positive_stabilizer fixes
  have stabilizer_zero : cycle (lift⁻¹ * matrix) = 0 := by
    rw [decomposition]
    exact cocycle_mul_eq_zero representation cycle _ _ (central_zero unit unit_positive) (rotations_zero angle)
  have product_zero := cocycle_mul_eq_zero representation cycle lift (lift⁻¹ * matrix)
    (sections_zero _) stabilizer_zero
  simpa only [mul_inv_cancel_left] using product_zero

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryUpperPotential_affine_unrestricted (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (point argument : UpperHalfPlane) :
    binaryUpperPotential cusp spherical basis level cycle ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
        binaryHilbertOperator cusp basis (binarySymmetricSection point)
          (binaryUpperPotential cusp spherical basis level cycle argument) := by
  have matrix_equality := binaryUpperSectionMatrix_affine_mul point argument point.im_pos argument.im_pos
  change binaryUpperSectionMatrix ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
    binaryUpperSectionMatrix point * binaryUpperSectionMatrix argument at matrix_equality
  rw [binaryUpperPotential, matrix_equality,
    invertibleMatrix_mul _ _ (binaryUpperSectionMatrix_invertible point point.im_pos)
      (binaryUpperSectionMatrix_invertible argument argument.im_pos),
    binaryUpperSectionMatrix_coe point, invertibleMatrix_coe]
  have identity := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property
    (binarySymmetricSection point) (invertibleMatrix (binaryUpperSectionMatrix argument))
  exact (congrArg Subtype.val identity).trans (add_comm _ _)

theorem binaryUpperPotential_zero_of_fderiv_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (base_zero : fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I = 0) :
    ∀ point : UpperHalfPlane, binaryUpperPotential cusp spherical basis level cycle point = 0 := by
  let potential := binaryUpperPotential cusp spherical basis level cycle
  have derivative_zero (point : UpperHalfPlane) : fderiv ℝ potential (point : ℂ) = 0 := by
    let affine : ℂ → ℂ := fun argument => (point.re : ℂ) + point.im • argument
    have affine_base : affine Complex.I = (point : ℂ) := by
      apply Complex.ext <;> simp [affine]
    have affine_derivative : HasFDerivAt affine (point.im • ContinuousLinearMap.id ℝ ℂ) Complex.I :=
      ((hasFDerivAt_id (𝕜 := ℝ) Complex.I).const_smul point.im).const_add (point.re : ℂ)
    have point_derivative : HasFDerivAt potential (fderiv ℝ potential (point : ℂ)) (point : ℂ) :=
      (regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos)).hasFDerivAt
    have base_derivative : HasFDerivAt (𝕜 := ℝ) potential 0 Complex.I := by
      have differentiable := regular.differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp))
      simpa only [potential, base_zero] using differentiable.hasFDerivAt
    have at_affine : HasFDerivAt potential (fderiv ℝ potential (point : ℂ)) (affine Complex.I) :=
      affine_base.symm ▸ point_derivative
    have left_derivative := at_affine.comp Complex.I affine_derivative
    let action := (binaryHilbertOperator cusp basis (binarySymmetricSection point)).restrictScalars ℝ
    have right_derivative : HasFDerivAt (𝕜 := ℝ)
        (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
          action (potential argument)) 0 Complex.I := by
      have derivative := (action.hasFDerivAt.comp Complex.I base_derivative).const_add
        (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val
      rw [ContinuousLinearMap.comp_zero] at derivative
      exact derivative
    have equality : potential ∘ affine =ᶠ[nhds Complex.I]
        (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
          action (potential argument)) := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
        (show Complex.I.im > 0 by simp)] with argument member
      exact binaryUpperPotential_affine_unrestricted cusp spherical basis level cycle point ⟨argument, member⟩
    have zero := left_derivative.unique (right_derivative.congr_of_eventuallyEq equality)
    apply ContinuousLinearMap.ext
    intro direction
    have scaled := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction) zero
    change fderiv ℝ potential (point : ℂ) (point.im • direction) = 0 at scaled
    rw [map_smul] at scaled
    exact (smul_eq_zero.mp scaled).resolve_left (ne_of_gt point.im_pos)
  have zero_derivative : Set.EqOn (fderiv ℝ potential) 0 UpperHalfPlane.upperHalfPlaneSet :=
    fun point member => derivative_zero ⟨point, member⟩
  have convex : Convex ℝ UpperHalfPlane.upperHalfPlaneSet :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  intro point
  have constant := UpperHalfPlane.isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    convex.isPreconnected regular zero_derivative point.im_pos (show Complex.I.im > 0 by simp)
  have basepoint : potential Complex.I = 0 := by
    simp only [potential, binaryUpperPotential, binaryAffineSection_I, groupCohomology.cocycles₁_map_one]
    rfl
  exact constant.trans basepoint

theorem binaryUpperPotential_fderiv_ne_zero_of_rotations (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (central_zero : ∀ unit : ℝˣ, 0 < unit.val → cycle (GeneralLinearGroup.scalar (Fin 2) unit) = 0) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I ≠ 0 := by
  intro zero
  apply nonzero
  apply binaryCocycle_H1_zero_of_positive_zero
  apply binaryCocycle_positive_zero_of_sections _ cycle _ rotations_zero central_zero
  intro point
  apply Subtype.ext
  have potential_zero := binaryUpperPotential_zero_of_fderiv_zero cusp spherical basis level cycle regular zero point
  rw [binaryUpperPotential_coe] at potential_zero
  exact potential_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
