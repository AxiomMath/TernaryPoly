module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart4
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ConnectedCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeNormalForm

@[expose] public section


/-!
# Level-three port of the spherical holomorphic-detection chain, Part5

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinaryRelativeNontrivial`, `SphericalDetection.BinaryConnectedCohomology`,
`SphericalDetection.BinaryRelativeNormalForm`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section CloneBinaryRelativeNontrivial

open GeneralEisenstein GeneralEisenstein.Adelic

variable {degree : ℕ} {index : Type} [Fintype index]

def binarySmoothTangent (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
      cycle matrix = 0)
    (direction : ℂ) : binarySmoothValues cusp index :=
  fun position => ⟨fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
    direction position,
    cuspAffineOrbitVector_coordinate_contDiffOn cusp basis _
      (binaryAffineOrbitVector_tangent_contDiffOn cusp spherical basis level cycle regular
        stabilizer_zero direction) position⟩

theorem binaryAntiholomorphicTangent_rotation (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
      cycle matrix = 0)
    (angle : Circle) :
    binaryHilbertOperator cusp basis (binaryRotations angle)
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
          Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
            Complex.I) =
      (angle : ℂ) ^ 2 •
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
          Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
            Complex.I) := by
  rw [map_add, map_smul, binaryUpperPotential_fderiv_rotation cusp spherical basis level cycle
    regular stabilizer_zero,
    binaryUpperPotential_fderiv_rotation cusp spherical basis level cycle regular stabilizer_zero,
      mul_one]
  have identity := realLinear_antiholomorphic_coordinates
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I).toLinearMap
      (((angle : ℂ) ^ 2)⁻¹)
  have conjugate_inverse : (starRingEnd ℂ) (((angle : ℂ) ^ 2)⁻¹) = (angle : ℂ) ^ 2 := by
    rw [map_inv₀, map_pow, ← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_pow, inv_inv]
  rw [conjugate_inverse] at identity
  exact identity

end CloneBinaryRelativeNontrivial

section CloneBinaryConnectedCohomology

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryUpperPotential_affine_unrestricted (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (point argument : UpperHalfPlane) :
    binaryUpperPotential cusp spherical basis level cycle ((point.re : ℂ) + (point.im : ℂ) *
      (argument : ℂ)) =
      (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
        binaryHilbertOperator cusp basis (binarySymmetricSection point)
          (binaryUpperPotential cusp spherical basis level cycle argument) := by
  have matrix_equality := binaryUpperSectionMatrix_affine_mul point argument point.im_pos
    argument.im_pos
  change binaryUpperSectionMatrix ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
    binaryUpperSectionMatrix point * binaryUpperSectionMatrix argument at matrix_equality
  rw [binaryUpperPotential, matrix_equality,
    invertibleMatrix_mul _ _ (binaryUpperSectionMatrix_invertible point point.im_pos)
      (binaryUpperSectionMatrix_invertible argument argument.im_pos),
    binaryUpperSectionMatrix_coe point, invertibleMatrix_coe]
  have identity := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property
    (binarySymmetricSection point) (invertibleMatrix (binaryUpperSectionMatrix argument))
  exact (congrArg Subtype.val identity).trans (add_comm _ _)

theorem binaryUpperPotential_zero_of_fderiv_zero (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
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
      (regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
        point.im_pos)).hasFDerivAt
    have base_derivative : HasFDerivAt (𝕜 := ℝ) potential 0 Complex.I := by
      have differentiable := regular.differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp))
      simpa only [potential, base_zero] using differentiable.hasFDerivAt
    have at_affine : HasFDerivAt potential (fderiv ℝ potential (point : ℂ)) (affine Complex.I) :=
      affine_base.symm ▸ point_derivative
    have left_derivative := at_affine.comp Complex.I affine_derivative
    let action := (binaryHilbertOperator cusp basis (binarySymmetricSection point)).restrictScalars
      ℝ
    have right_derivative : HasFDerivAt (𝕜 := ℝ)
        (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp
          level).val +
          action (potential argument)) 0 Complex.I := by
      have derivative := (action.hasFDerivAt.comp Complex.I base_derivative).const_add
        (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val
      rw [ContinuousLinearMap.comp_zero] at derivative
      exact derivative
    have equality : potential ∘ affine =ᶠ[nhds Complex.I]
        (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp
          level).val +
          action (potential argument)) := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
        (show Complex.I.im > 0 by simp)] with argument member
      exact binaryUpperPotential_affine_unrestricted cusp spherical basis level cycle point
        ⟨argument, member⟩
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
    simp only [potential, binaryUpperPotential, binaryAffineSection_I,
      groupCohomology.cocycles₁_map_one]
    rfl
  exact constant.trans basepoint

theorem binaryUpperPotential_fderiv_ne_zero_of_rotations (cusp : CuspidalRepresentation) (spherical
    : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (central_zero : ∀ unit : ℝˣ, 0 < unit.val → cycle (GeneralLinearGroup.scalar (Fin 2) unit) = 0)
      :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I ≠ 0 := by
  intro zero
  apply nonzero
  apply binaryCocycle_H1_zero_of_positive_zero
  apply binaryCocycle_positive_zero_of_sections _ cycle _ rotations_zero central_zero
  intro point
  apply Subtype.ext
  have potential_zero := binaryUpperPotential_zero_of_fderiv_zero cusp spherical basis level cycle
    regular zero point
  rw [binaryUpperPotential_coe] at potential_zero
  exact potential_zero

end CloneBinaryConnectedCohomology

section CloneBinaryRelativeNormalForm

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cohomological_exists_relative_normal_form (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis
        (degree + 1)) level))
      (lower upper : binarySmoothValues cusp (Fin (degree + 2))),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1))
        level) cycle ≠ 0 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
          UpperHalfPlane.upperHalfPlaneSet ∧
      (∀ angle : Circle, cycle (binaryRotations angle) = 0) ∧
      (∀ unit : ℝˣ, 0 < unit.val → cycle (Matrix.GeneralLinearGroup.scalar (Fin 2) unit) = 0) ∧
      (∀ position, lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree
        (-2) position)) ∧
      (∀ position, upper position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 2
        position)) ∧
      binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical
        (binaryWeightBasis (degree + 1)) level cycle ∧
      binarySmoothValues_val cusp upper =
        fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
          Complex.I 1 +
          Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree +
            1)) level cycle) Complex.I Complex.I ∧
      binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
        binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper ∧
      (∀ position : Fin (degree + 1), lower position.succ = 0) ∧
      (lower ≠ 0 ∨ upper ≠ 0) := by
  let basis := binaryWeightBasis (degree + 1)
  obtain ⟨level, original, level_open, level_compact, nonzero, regular, stabilizer_zero, _⟩ :=
    cohomological_exists_symmetric_basepoint_differential cusp spherical cohomological basis
  let first := binarySmoothTangent cusp spherical basis level original regular stabilizer_zero 1
  let second := binarySmoothTangent cusp spherical basis level original regular stabilizer_zero
    Complex.I
  let lower := first - Complex.I • second
  let upper := first + Complex.I • second
  have differentiable := regular.differentiableOn (by simp)
  have lower_value : binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical
    basis level original := rfl
  have upper_value : binarySmoothValues_val cusp upper =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level original) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level original) Complex.I
          Complex.I := rfl
  have finite_fixed (element : level) (position : Fin (degree + 2)) :
      cusp.π (atFinite element.val) (lower position).val = (lower position).val ∧
        cusp.π (atFinite element.val) (upper position).val = (upper position).val := by
    have first_fixed := binaryUpperPotential_fderiv_finiteLevel cusp spherical basis level original
      differentiable element 1 position
    have second_fixed := binaryUpperPotential_fderiv_finiteLevel cusp spherical basis level
      original differentiable element Complex.I position
    change cusp.π (atFinite element.val) (first position).val = (first position).val at first_fixed
    change cusp.π (atFinite element.val) (second position).val = (second
      position).val at second_fixed
    change cusp.π (atFinite element.val) (_ - Complex.I • _) = _ ∧ cusp.π (atFinite element.val) (_
      + Complex.I • _) = _
    constructor
    · rw [map_sub, map_smul, first_fixed, second_fixed]
      rfl
    · rw [map_add, map_smul, first_fixed, second_fixed]
      rfl
  have lower_rotation (angle : Circle) :
      binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp lower) =
        (angle : ℂ) ^ (-2 : ℤ) • binarySmoothValues_val cusp lower := by
    rw [lower_value]
    simpa only [zpow_neg, zpow_ofNat] using
      binaryHolomorphicTangent_rotation cusp spherical basis level original differentiable
        stabilizer_zero angle
  have upper_rotation (angle : Circle) :
      binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp upper) =
        (angle : ℂ) ^ (2 : ℤ) • binarySmoothValues_val cusp upper := by
    rw [upper_value]
    exact binaryAntiholomorphicTangent_rotation cusp spherical basis level original differentiable
      stabilizer_zero angle
  have lower_mem (position : Fin (degree + 2)) :
      lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (-2) position)
        :=
    ⟨fun element => (finite_fixed element position).1,
      binaryWeightBasis_eigenvector_coordinate cusp degree (-2) _ lower_rotation position⟩
  have upper_mem (position : Fin (degree + 2)) :
      upper position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 2 position) :=
    ⟨fun element => (finite_fixed element position).2,
      binaryWeightBasis_eigenvector_coordinate cusp degree 2 _ upper_rotation position⟩
  have closed : binaryRelativeRaising cusp basis (-2) lower = binaryRelativeLowering cusp basis 2
    upper := by
    apply (binaryRelative_cocycle_iff cusp basis first second).mpr
    apply binarySmoothValues_val_injective cusp
    rw [map_sub, binaryTensorDifferential_actual, binaryTensorDifferential_actual]
    exact binaryTangent_relativeCocycle cusp spherical basis level original regular stabilizer_zero
  obtain ⟨primitive, _, primitive_mem, eliminated⟩ := binaryRelativeLowering_eliminate cusp degree
    level lower lower_mem
  let finite_primitive : binaryHilbertFiniteValues (index := Fin (degree + 2)) cusp level :=
    ⟨binarySmoothValues_val cusp primitive, fun element position => (primitive_mem position).1
      element⟩
  let shifted := shiftCocycle (binaryHilbertFiniteRep cusp spherical basis level) original
    finite_primitive
  let new_lower := lower - binaryRelativeLowering cusp basis 0 primitive
  let new_upper := upper - binaryRelativeRaising cusp basis 0 primitive
  have shifted_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
    shifted ≠ 0 := by
    intro zero
    exact nonzero ((shiftCocycle_H1 _ original finite_primitive).symm.trans zero)
  have primitive_regular := binarySmoothValues_regular cusp basis primitive
  have shifted_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical basis level shifted) UpperHalfPlane.upperHalfPlaneSet :=
        by
    rw [show shifted = shiftCocycle _ original finite_primitive from rfl,
      binaryUpperPotential_shift]
    exact regular.sub (primitive_regular.sub contDiffOn_const)
  have shifted_rotations (angle : Circle) : shifted (binaryRotations angle) = 0 := by
    apply shiftCocycle_zero_of_fixed _ _ _ _ (stabilizer_zero _ (binaryRotations_smul_I angle))
    apply Subtype.ext
    change binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp
      primitive) =
      binarySmoothValues_val cusp primitive
    have fixed := binaryFiniteWeightValues_rotation cusp degree level 0 primitive primitive_mem
      angle
    simpa only [zpow_zero, one_smul] using fixed
  have shifted_central := binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical
    cohomological basis level
    level_open level_compact shifted
  have neighborhood := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by
    simp)
  have shifted_derivative := binaryUpperPotential_shift_fderiv cusp spherical basis level original
    finite_primitive
    (differentiable.differentiableAt neighborhood)
    ((primitive_regular.differentiableOn (by simp)).differentiableAt neighborhood)
  have new_lower_value : binarySmoothValues_val cusp new_lower = binaryHolomorphicTangent cusp
    spherical basis level shifted := by
    rw [show new_lower = lower - binaryRelativeLowering cusp basis 0 primitive from rfl, map_sub,
      lower_value, binaryRelativeLowering_actual, binaryHolomorphicTangent,
        binaryHolomorphicTangent]
    rw [show shifted = shiftCocycle _ original finite_primitive from rfl, shifted_derivative]
    simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero, _root_.sub_apply]
    change _ = (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
      primitive)) Complex.I 1) -
      Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
        primitive)) Complex.I Complex.I)
    module
  have new_upper_value : binarySmoothValues_val cusp new_upper =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I
          Complex.I := by
    rw [show new_upper = upper - binaryRelativeRaising cusp basis 0 primitive from rfl, map_sub,
      upper_value, binaryRelativeRaising_actual]
    rw [show shifted = shiftCocycle _ original finite_primitive from rfl, shifted_derivative]
    simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero, _root_.sub_apply]
    change _ = (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
      primitive)) Complex.I 1) +
      Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp
        primitive)) Complex.I Complex.I)
    module
  refine ⟨level, shifted, new_lower, new_upper, level_open, level_compact, shifted_nonzero,
    shifted_regular, shifted_rotations, shifted_central, ?_, ?_, new_lower_value, new_upper_value,
    binaryRelativeLadder_shift cusp basis lower upper primitive closed, eliminated, ?_⟩
  · intro position
    exact Submodule.sub_mem _ (lower_mem position) (binaryRelativeLowering_mem cusp degree level 0
      primitive primitive_mem position)
  · intro position
    exact Submodule.sub_mem _ (upper_mem position) (binaryRelativeRaising_mem cusp degree level 0
      primitive primitive_mem position)
  · by_contra both_zero
    push Not at both_zero
    have lower_zero := (new_lower_value.symm.trans (congrArg (binarySmoothValues_val cusp)
      both_zero.1)).trans (map_zero _)
    have upper_zero := (new_upper_value.symm.trans (congrArg (binarySmoothValues_val cusp)
      both_zero.2)).trans (map_zero _)
    have derivative_zero := realLinear_eq_zero_of_tangent_pair
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I).toLinearMap
        lower_zero upper_zero
    apply binaryUpperPotential_fderiv_ne_zero_of_rotations cusp spherical basis level shifted
      shifted_nonzero
      (shifted_regular.differentiableOn (by simp)) shifted_rotations shifted_central
    apply ContinuousLinearMap.ext
    intro direction
    exact LinearMap.congr_fun derivative_zero direction

end CloneBinaryRelativeNormalForm

end TernaryPeriodPolynomials.MultiplicityOne
