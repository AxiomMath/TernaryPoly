module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeNormalForm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryRelativePair_coboundary_iff (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (lower upper : binarySmoothValues cusp index)
    (lower_value : binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical basis level cycle)
    (upper_value : binarySmoothValues_val cusp upper =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I) :
    groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle = 0 ↔
      ∃ primitive : binarySmoothValues cusp index,
        (∀ element : level, ∀ position, cusp.π (atFinite element.val) (primitive position).val = (primitive position).val) ∧
        (∀ angle : Circle, binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp primitive) =
          binarySmoothValues_val cusp primitive) ∧
        binaryRelativeLowering cusp basis 0 primitive = lower ∧
        binaryRelativeRaising cusp basis 0 primitive = upper := by
  have neighborhood := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp)
  constructor
  · intro zero
    obtain ⟨finite_primitive, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp zero
    have potential : binaryUpperPotential cusp spherical basis level cycle =
        fun point => binaryAffineOrbitVector cusp basis finite_primitive.val point - finite_primitive.val := by
      funext point
      exact (congrArg Subtype.val (congrFun boundary (invertibleMatrix (binaryUpperSectionMatrix point)))).symm
    have primitive_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (binaryAffineOrbitVector cusp basis finite_primitive.val) UpperHalfPlane.upperHalfPlaneSet := by
      apply (regular.add (contDiffOn_const (c := finite_primitive.val))).congr
      intro point _
      rw [potential]
      simp only [sub_add_cancel]
    let primitive : binarySmoothValues cusp index := fun position =>
      ⟨finite_primitive.val position, cuspAffineOrbitVector_coordinate_contDiffOn cusp basis _ primitive_regular position⟩
    have primitive_value : binarySmoothValues_val cusp primitive = finite_primitive.val := rfl
    have derivative := (((primitive_regular.differentiableOn (by simp)).differentiableAt neighborhood).hasFDerivAt.sub_const
      finite_primitive.val).fderiv
    have lower_derivative : binarySmoothValues_val cusp (binaryRelativeLowering cusp basis 0 primitive) =
        binarySmoothValues_val cusp lower := by
      rw [binaryRelativeLowering_actual, lower_value, binaryHolomorphicTangent, potential, derivative, primitive_value]
      simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero]
    have upper_derivative : binarySmoothValues_val cusp (binaryRelativeRaising cusp basis 0 primitive) =
        binarySmoothValues_val cusp upper := by
      rw [binaryRelativeRaising_actual, upper_value, potential, derivative, primitive_value]
      simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero]
    refine ⟨primitive, finite_primitive.property, ?_,
      binarySmoothValues_val_injective cusp lower_derivative, binarySmoothValues_val_injective cusp upper_derivative⟩
    intro angle
    have identity := congrArg Subtype.val (congrFun boundary (binaryRotations angle))
    change binaryHilbertOperator cusp basis (binaryRotations angle) finite_primitive.val - finite_primitive.val =
      (cycle (binaryRotations angle) : binaryHilbertFiniteValues cusp level).val at identity
    rw [rotations_zero] at identity
    exact sub_eq_zero.mp identity
  · rintro ⟨primitive, primitive_finite, primitive_rotation, primitive_lower, primitive_upper⟩
    by_contra nonzero
    let finite_primitive : binaryHilbertFiniteValues (index := index) cusp level :=
      ⟨binarySmoothValues_val cusp primitive, primitive_finite⟩
    let shifted := shiftCocycle (binaryHilbertFiniteRep cusp spherical basis level) cycle finite_primitive
    have shifted_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) shifted ≠ 0 := by
      intro zero
      exact nonzero ((shiftCocycle_H1 _ cycle finite_primitive).symm.trans zero)
    have primitive_regular := binarySmoothValues_regular cusp basis primitive
    have shifted_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (binaryUpperPotential cusp spherical basis level shifted) UpperHalfPlane.upperHalfPlaneSet := by
      rw [show shifted = shiftCocycle _ cycle finite_primitive from rfl, binaryUpperPotential_shift]
      exact regular.sub (primitive_regular.sub contDiffOn_const)
    have shifted_rotations (angle : Circle) : shifted (binaryRotations angle) = 0 := by
      apply shiftCocycle_zero_of_fixed _ _ _ _ (rotations_zero angle)
      exact Subtype.ext (primitive_rotation angle)
    have shifted_central := binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical cohomological basis level
      level_open level_compact shifted
    have shifted_derivative := binaryUpperPotential_shift_fderiv cusp spherical basis level cycle finite_primitive
      ((regular.differentiableOn (by simp)).differentiableAt neighborhood)
      ((primitive_regular.differentiableOn (by simp)).differentiableAt neighborhood)
    have lower_derivative := congrArg (binarySmoothValues_val cusp) primitive_lower
    have upper_derivative := congrArg (binarySmoothValues_val cusp) primitive_upper
    rw [binaryRelativeLowering_actual, lower_value, binaryHolomorphicTangent] at lower_derivative
    rw [binaryRelativeRaising_actual, upper_value] at upper_derivative
    simp only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero] at lower_derivative upper_derivative
    let difference := fderiv ℝ (binaryUpperPotential cusp spherical basis level shifted) Complex.I
    have lower_zero : difference 1 - Complex.I • difference Complex.I = 0 := by
      dsimp only [difference]
      rw [show shifted = shiftCocycle _ cycle finite_primitive from rfl, shifted_derivative]
      change (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I 1) -
        Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I Complex.I) = 0
      have zero := sub_eq_zero.mpr lower_derivative.symm
      convert zero using 1
      module
    have upper_zero : difference 1 + Complex.I • difference Complex.I = 0 := by
      dsimp only [difference]
      rw [show shifted = shiftCocycle _ cycle finite_primitive from rfl, shifted_derivative]
      change (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I 1) +
        Complex.I • (_ - fderiv ℝ (binaryAffineOrbitVector cusp basis (binarySmoothValues_val cusp primitive)) Complex.I Complex.I) = 0
      have zero := sub_eq_zero.mpr upper_derivative.symm
      convert zero using 1
      module
    have zero := realLinear_eq_zero_of_tangent_pair difference.toLinearMap lower_zero upper_zero
    apply binaryUpperPotential_fderiv_ne_zero_of_rotations cusp spherical basis level shifted shifted_nonzero
      (shifted_regular.differentiableOn (by simp)) shifted_rotations shifted_central
    apply ContinuousLinearMap.ext
    exact LinearMap.congr_fun zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
