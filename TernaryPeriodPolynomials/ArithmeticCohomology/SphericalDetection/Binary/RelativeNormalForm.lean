module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeElimination
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeWeightValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeCommutator
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ConnectedCohomology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realLinear_eq_zero_of_tangent_pair {E : Type} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] (linear : ℂ →ₗ[ℝ] E)
    (lower_zero : linear 1 - Complex.I • linear Complex.I = 0)
    (upper_zero : linear 1 + Complex.I • linear Complex.I = 0) : linear = 0 := by
  have twice : (2 : ℂ) • linear 1 = 0 := by
    calc
      _ = (linear 1 - Complex.I • linear Complex.I) + (linear 1 + Complex.I • linear Complex.I) := by module
      _ = 0 := by rw [lower_zero, upper_zero, add_zero]
  have first_zero : linear 1 = 0 := (smul_eq_zero.mp twice).resolve_left (by norm_num)
  have second_zero : linear Complex.I = 0 := by
    rw [first_zero, zero_add] at upper_zero
    exact (smul_eq_zero.mp upper_zero).resolve_left Complex.I_ne_zero
  ext direction
  rw [realLinear_complex_coordinates linear direction, first_zero, second_zero, smul_zero, smul_zero, add_zero]
  rfl

theorem cohomological_exists_relative_normal_form (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level))
      (lower upper : binarySmoothValues cusp (Fin (degree + 2))),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level) cycle ≠ 0 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) UpperHalfPlane.upperHalfPlaneSet ∧
      (∀ angle : Circle, cycle (binaryRotations angle) = 0) ∧
      (∀ unit : ℝˣ, 0 < unit.val → cycle (Matrix.GeneralLinearGroup.scalar (Fin 2) unit) = 0) ∧
      (∀ position, lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (-2) position)) ∧
      (∀ position, upper position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 2 position)) ∧
      binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical (binaryWeightBasis (degree + 1)) level cycle ∧
      binarySmoothValues_val cusp upper =
        fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) Complex.I 1 +
          Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) Complex.I Complex.I ∧
      binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
        binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper ∧
      (∀ position : Fin (degree + 1), lower position.succ = 0) ∧
      (lower ≠ 0 ∨ upper ≠ 0) := by
  let basis := binaryWeightBasis (degree + 1)
  obtain ⟨level, original, level_open, level_compact, nonzero, regular, stabilizer_zero, _⟩ :=
    cohomological_exists_symmetric_basepoint_differential cusp spherical cohomological basis
  let first := binarySmoothTangent cusp spherical basis level original regular stabilizer_zero 1
  let second := binarySmoothTangent cusp spherical basis level original regular stabilizer_zero Complex.I
  let lower := first - Complex.I • second
  let upper := first + Complex.I • second
  have differentiable := regular.differentiableOn (by simp)
  have lower_value : binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical basis level original := rfl
  have upper_value : binarySmoothValues_val cusp upper =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level original) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level original) Complex.I Complex.I := rfl
  have finite_fixed (element : level) (position : Fin (degree + 2)) :
      cusp.π (atFinite element.val) (lower position).val = (lower position).val ∧
        cusp.π (atFinite element.val) (upper position).val = (upper position).val := by
    have first_fixed := binaryUpperPotential_fderiv_finiteLevel cusp spherical basis level original differentiable element 1 position
    have second_fixed := binaryUpperPotential_fderiv_finiteLevel cusp spherical basis level original differentiable element Complex.I position
    change cusp.π (atFinite element.val) (first position).val = (first position).val at first_fixed
    change cusp.π (atFinite element.val) (second position).val = (second position).val at second_fixed
    change cusp.π (atFinite element.val) (_ - Complex.I • _) = _ ∧ cusp.π (atFinite element.val) (_ + Complex.I • _) = _
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
      binaryHolomorphicTangent_rotation cusp spherical basis level original differentiable stabilizer_zero angle
  have upper_rotation (angle : Circle) :
      binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp upper) =
        (angle : ℂ) ^ (2 : ℤ) • binarySmoothValues_val cusp upper := by
    rw [upper_value]
    exact binaryAntiholomorphicTangent_rotation cusp spherical basis level original differentiable stabilizer_zero angle
  have lower_mem (position : Fin (degree + 2)) :
      lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (-2) position) :=
    ⟨fun element => (finite_fixed element position).1,
      binaryWeightBasis_eigenvector_coordinate cusp degree (-2) _ lower_rotation position⟩
  have upper_mem (position : Fin (degree + 2)) :
      upper position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 2 position) :=
    ⟨fun element => (finite_fixed element position).2,
      binaryWeightBasis_eigenvector_coordinate cusp degree 2 _ upper_rotation position⟩
  have closed : binaryRelativeRaising cusp basis (-2) lower = binaryRelativeLowering cusp basis 2 upper := by
    apply (binaryRelative_cocycle_iff cusp basis first second).mpr
    apply binarySmoothValues_val_injective cusp
    rw [map_sub, binaryTensorDifferential_actual, binaryTensorDifferential_actual]
    exact binaryTangent_relativeCocycle cusp spherical basis level original regular stabilizer_zero
  obtain ⟨primitive, _, primitive_mem, eliminated⟩ := binaryRelativeLowering_eliminate cusp degree level lower lower_mem
  let finite_primitive : binaryHilbertFiniteValues (index := Fin (degree + 2)) cusp level :=
    ⟨binarySmoothValues_val cusp primitive, fun element position => (primitive_mem position).1 element⟩
  let shifted := shiftCocycle (binaryHilbertFiniteRep cusp spherical basis level) original finite_primitive
  let new_lower := lower - binaryRelativeLowering cusp basis 0 primitive
  let new_upper := upper - binaryRelativeRaising cusp basis 0 primitive
  have shifted_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) shifted ≠ 0 := by
    intro zero
    exact nonzero ((shiftCocycle_H1 _ original finite_primitive).symm.trans zero)
  have primitive_regular := binarySmoothValues_regular cusp basis primitive
  have shifted_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical basis level shifted) UpperHalfPlane.upperHalfPlaneSet := by
    rw [show shifted = shiftCocycle _ original finite_primitive from rfl, binaryUpperPotential_shift]
    exact regular.sub (primitive_regular.sub contDiffOn_const)
  have shifted_rotations (angle : Circle) : shifted (binaryRotations angle) = 0 := by
    apply shiftCocycle_zero_of_fixed _ _ _ _ (stabilizer_zero _ (binaryRotations_smul_I angle))
    apply Subtype.ext
    change binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp primitive) =
      binarySmoothValues_val cusp primitive
    have fixed := binaryFiniteWeightValues_rotation cusp degree level 0 primitive primitive_mem angle
    simpa only [zpow_zero, one_smul] using fixed
  have shifted_central := binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical cohomological basis level
    level_open level_compact shifted
  have neighborhood := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp)
  have shifted_derivative := binaryUpperPotential_shift_fderiv cusp spherical basis level original finite_primitive
    (differentiable.differentiableAt neighborhood)
    ((primitive_regular.differentiableOn (by simp)).differentiableAt neighborhood)
  have new_lower_value : binarySmoothValues_val cusp new_lower = binaryHolomorphicTangent cusp spherical basis level shifted := by
    rw [show new_lower = lower - binaryRelativeLowering cusp basis 0 primitive from rfl, map_sub,
      lower_value, binaryRelativeLowering_actual, binaryHolomorphicTangent, binaryHolomorphicTangent]
    rw [show shifted = shiftCocycle _ original finite_primitive from rfl, shifted_derivative]
    simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero, _root_.sub_apply]
    change _ = (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I 1) -
      Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I Complex.I)
    module
  have new_upper_value : binarySmoothValues_val cusp new_upper =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I Complex.I := by
    rw [show new_upper = upper - binaryRelativeRaising cusp basis 0 primitive from rfl, map_sub,
      upper_value, binaryRelativeRaising_actual]
    rw [show shifted = shiftCocycle _ original finite_primitive from rfl, shifted_derivative]
    simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero, _root_.sub_apply]
    change _ = (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I 1) +
      Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I Complex.I)
    module
  refine ⟨level, shifted, new_lower, new_upper, level_open, level_compact, shifted_nonzero,
    shifted_regular, shifted_rotations, shifted_central, ?_, ?_, new_lower_value, new_upper_value,
    binaryRelativeLadder_shift cusp basis lower upper primitive closed, eliminated, ?_⟩
  · intro position
    exact Submodule.sub_mem _ (lower_mem position) (binaryRelativeLowering_mem cusp degree level 0 primitive primitive_mem position)
  · intro position
    exact Submodule.sub_mem _ (upper_mem position) (binaryRelativeRaising_mem cusp degree level 0 primitive primitive_mem position)
  · by_contra both_zero
    push Not at both_zero
    have lower_zero := (new_lower_value.symm.trans (congrArg (binarySmoothValues_val cusp) both_zero.1)).trans (map_zero _)
    have upper_zero := (new_upper_value.symm.trans (congrArg (binarySmoothValues_val cusp) both_zero.2)).trans (map_zero _)
    have derivative_zero := realLinear_eq_zero_of_tangent_pair
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I).toLinearMap lower_zero upper_zero
    apply binaryUpperPotential_fderiv_ne_zero_of_rotations cusp spherical basis level shifted shifted_nonzero
      (shifted_regular.differentiableOn (by simp)) shifted_rotations shifted_central
    apply ContinuousLinearMap.ext
    intro direction
    exact LinearMap.congr_fun derivative_zero direction

end TernaryPeriodPolynomials.SphericalDetection.Helpers
