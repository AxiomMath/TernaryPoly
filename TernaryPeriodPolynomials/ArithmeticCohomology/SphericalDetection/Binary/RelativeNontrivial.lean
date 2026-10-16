module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeOperators
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderAlgebra

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

def binarySmoothTangent (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (direction : ℂ) : binarySmoothValues cusp index :=
  fun position => ⟨fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction position,
    cuspAffineOrbitVector_coordinate_contDiffOn cusp basis _
      (binaryAffineOrbitVector_tangent_contDiffOn cusp spherical basis level cycle regular stabilizer_zero direction) position⟩

theorem binarySmoothTangent_val (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (direction : ℂ) :
    binarySmoothValues_val cusp (binarySmoothTangent cusp spherical basis level cycle regular stabilizer_zero direction) =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction := rfl

theorem binaryAntiholomorphicTangent_rotation (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (angle : Circle) :
    binaryHilbertOperator cusp basis (binaryRotations angle)
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
          Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I) =
      (angle : ℂ) ^ 2 •
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
          Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I) := by
  rw [map_add, map_smul, binaryUpperPotential_fderiv_rotation cusp spherical basis level cycle regular stabilizer_zero,
    binaryUpperPotential_fderiv_rotation cusp spherical basis level cycle regular stabilizer_zero, mul_one]
  have identity := realLinear_antiholomorphic_coordinates
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I).toLinearMap (((angle : ℂ) ^ 2)⁻¹)
  have conjugate_inverse : (starRingEnd ℂ) (((angle : ℂ) ^ 2)⁻¹) = (angle : ℂ) ^ 2 := by
    rw [map_inv₀, map_pow, ← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_pow, inv_inv]
  rw [conjugate_inverse] at identity
  exact identity

theorem cohomological_exists_nontrivial_relative_ladder_pair (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL) (lower upper : binarySmoothValues cusp index),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧ lower ≠ 0 ∧
      (∀ element : level, ∀ position,
        cusp.π (atFinite element.val) (lower position).val = (lower position).val ∧
        cusp.π (atFinite element.val) (upper position).val = (upper position).val) ∧
      (∀ angle : Circle,
        binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp lower) =
          ((angle : ℂ) ^ 2)⁻¹ • binarySmoothValues_val cusp lower) ∧
      (∀ angle : Circle,
        binaryHilbertOperator cusp basis (binaryRotations angle) (binarySmoothValues_val cusp upper) =
          (angle : ℂ) ^ 2 • binarySmoothValues_val cusp upper) ∧
      binaryRelativeRaising cusp basis (-2) lower = binaryRelativeLowering cusp basis 2 upper ∧
      ¬∃ primitive : binarySmoothValues cusp index,
        (∀ element : level, ∀ position,
          cusp.π (atFinite element.val) (primitive position).val = (primitive position).val) ∧
        (∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
          binaryHilbertOperator cusp basis matrix (binarySmoothValues_val cusp primitive) = binarySmoothValues_val cusp primitive) ∧
        binaryRelativeLowering cusp basis 0 primitive = lower := by
  obtain ⟨level, cycle, level_open, level_compact, nonzero, regular, stabilizer_zero, _⟩ :=
    cohomological_exists_symmetric_basepoint_differential cusp spherical cohomological basis
  let first := binarySmoothTangent cusp spherical basis level cycle regular stabilizer_zero 1
  let second := binarySmoothTangent cusp spherical basis level cycle regular stabilizer_zero Complex.I
  let lower := first - Complex.I • second
  let upper := first + Complex.I • second
  have differentiable := regular.differentiableOn (by simp)
  have lower_value : binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical basis level cycle := rfl
  have upper_value : binarySmoothValues_val cusp upper =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I := rfl
  refine ⟨level, lower, upper, level_open, level_compact, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro zero
    have value_zero := congrArg (binarySmoothValues_val cusp) zero
    rw [lower_value, map_zero] at value_zero
    exact binaryHolomorphicTangent_nonzero cusp spherical basis level cycle nonzero differentiable stabilizer_zero value_zero
  · intro element position
    have first_fixed := binaryUpperPotential_fderiv_finiteLevel cusp spherical basis level cycle differentiable element 1 position
    have second_fixed := binaryUpperPotential_fderiv_finiteLevel cusp spherical basis level cycle differentiable element Complex.I position
    change cusp.π (atFinite element.val) (first position).val = (first position).val at first_fixed
    change cusp.π (atFinite element.val) (second position).val = (second position).val at second_fixed
    change cusp.π (atFinite element.val) (_ - Complex.I • _) = _ ∧
      cusp.π (atFinite element.val) (_ + Complex.I • _) = _
    constructor
    · rw [map_sub, map_smul, first_fixed, second_fixed]
      rfl
    · rw [map_add, map_smul, first_fixed, second_fixed]
      rfl
  · intro angle
    rw [lower_value]
    exact binaryHolomorphicTangent_rotation cusp spherical basis level cycle differentiable stabilizer_zero angle
  · intro angle
    rw [upper_value]
    exact binaryAntiholomorphicTangent_rotation cusp spherical basis level cycle differentiable stabilizer_zero angle
  · apply (binaryRelative_cocycle_iff cusp basis first second).mpr
    apply binarySmoothValues_val_injective cusp
    rw [map_sub, binaryTensorDifferential_actual, binaryTensorDifferential_actual]
    exact binaryTangent_relativeCocycle cusp spherical basis level cycle regular stabilizer_zero
  · rintro ⟨primitive, primitive_finite, primitive_fixed, primitive_lower⟩
    let finite_primitive : binaryHilbertFiniteValues (index := index) cusp level :=
      ⟨binarySmoothValues_val cusp primitive, primitive_finite⟩
    apply binaryHolomorphicTangent_not_coboundary cusp spherical basis level cycle nonzero differentiable stabilizer_zero
      finite_primitive ((binarySmoothValues_regular cusp basis primitive).differentiableOn (by simp)) primitive_fixed
    have equality := congrArg (binarySmoothValues_val cusp) primitive_lower
    rw [binaryRelativeLowering_actual, lower_value] at equality
    simpa only [Int.cast_zero, mul_zero, zero_div, zero_smul, add_zero] using equality.symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
