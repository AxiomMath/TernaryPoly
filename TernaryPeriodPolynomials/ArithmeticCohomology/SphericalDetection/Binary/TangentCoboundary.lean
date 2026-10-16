module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryUpperPotential_shift (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (primitive : binaryHilbertFiniteValues (index := index) cusp level) :
    binaryUpperPotential cusp spherical basis level (shiftCocycle _ cycle primitive) =
      fun point => binaryUpperPotential cusp spherical basis level cycle point -
        (binaryAffineOrbitVector cusp basis primitive.val point - primitive.val) := rfl

theorem binaryUpperPotential_shift_fderiv (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (primitive : binaryHilbertFiniteValues (index := index) cusp level)
    (cycle_regular : DifferentiableAt ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I)
    (primitive_regular : DifferentiableAt ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level (shiftCocycle _ cycle primitive)) Complex.I =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I -
        fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I := by
  rw [binaryUpperPotential_shift]
  exact (cycle_regular.hasFDerivAt.sub (primitive_regular.hasFDerivAt.sub_const primitive.val)).fderiv

theorem binaryUpperPotential_fderiv_not_coboundary (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (primitive : binaryHilbertFiniteValues (index := index) cusp level)
    (primitive_regular : DifferentiableOn ℝ (binaryAffineOrbitVector cusp basis primitive.val) UpperHalfPlane.upperHalfPlaneSet)
    (primitive_fixed : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
      binaryHilbertOperator cusp basis matrix primitive.val = primitive.val) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I ≠
      fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I := by
  have shifted_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
      (shiftCocycle _ cycle primitive) ≠ 0 := by
    intro zero
    exact nonzero ((shiftCocycle_H1 _ cycle primitive).symm.trans zero)
  have shifted_regular : DifferentiableOn ℝ
      (binaryUpperPotential cusp spherical basis level (shiftCocycle _ cycle primitive)) UpperHalfPlane.upperHalfPlaneSet := by
    rw [binaryUpperPotential_shift]
    exact regular.sub (primitive_regular.sub_const primitive.val)
  have shifted_stabilizer : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
      shiftCocycle (binaryHilbertFiniteRep cusp spherical basis level) cycle primitive matrix = 0 := by
    intro matrix stabilizes
    apply shiftCocycle_zero_of_fixed _ _ _ _ (stabilizer_zero matrix stabilizes)
    exact Subtype.ext (primitive_fixed matrix stabilizes)
  have derivative_nonzero := binaryUpperPotential_fderiv_basepoint_ne_zero cusp spherical basis level
    (shiftCocycle _ cycle primitive) shifted_nonzero shifted_regular shifted_stabilizer
  have neighborhood := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp)
  rw [binaryUpperPotential_shift_fderiv cusp spherical basis level cycle primitive
    (regular.differentiableAt neighborhood) (primitive_regular.differentiableAt neighborhood), sub_ne_zero] at derivative_nonzero
  exact derivative_nonzero

theorem binaryHolomorphicTangent_not_coboundary (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (primitive : binaryHilbertFiniteValues (index := index) cusp level)
    (primitive_regular : DifferentiableOn ℝ (binaryAffineOrbitVector cusp basis primitive.val) UpperHalfPlane.upperHalfPlaneSet)
    (primitive_fixed : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
      binaryHilbertOperator cusp basis matrix primitive.val = primitive.val) :
    binaryHolomorphicTangent cusp spherical basis level cycle ≠
      fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I 1 -
        Complex.I • fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I Complex.I := by
  have shifted_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
      (shiftCocycle _ cycle primitive) ≠ 0 := by
    intro zero
    exact nonzero ((shiftCocycle_H1 _ cycle primitive).symm.trans zero)
  have shifted_regular : DifferentiableOn ℝ
      (binaryUpperPotential cusp spherical basis level (shiftCocycle _ cycle primitive)) UpperHalfPlane.upperHalfPlaneSet := by
    rw [binaryUpperPotential_shift]
    exact regular.sub (primitive_regular.sub_const primitive.val)
  have shifted_stabilizer : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
      shiftCocycle (binaryHilbertFiniteRep cusp spherical basis level) cycle primitive matrix = 0 := by
    intro matrix stabilizes
    apply shiftCocycle_zero_of_fixed _ _ _ _ (stabilizer_zero matrix stabilizes)
    exact Subtype.ext (primitive_fixed matrix stabilizes)
  have tangent_nonzero := binaryHolomorphicTangent_nonzero cusp spherical basis level
    (shiftCocycle _ cycle primitive) shifted_nonzero shifted_regular shifted_stabilizer
  have neighborhood := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp)
  intro equality
  apply tangent_nonzero
  rw [binaryHolomorphicTangent, binaryUpperPotential_shift_fderiv cusp spherical basis level cycle primitive
    (regular.differentiableAt neighborhood) (primitive_regular.differentiableAt neighborhood)]
  change (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 -
      fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I 1) -
    Complex.I • (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I -
      fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I Complex.I) = 0
  rw [smul_sub]
  change (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 -
      fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I 1) -
    (Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I -
      Complex.I • fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I Complex.I) = 0
  have zero := sub_eq_zero.mpr equality
  change (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 -
      Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I) -
    (fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I 1 -
      Complex.I • fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I Complex.I) = 0 at zero
  convert zero using 1
  abel

theorem binaryHolomorphicTangent_coboundary_iff (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle = 0 ↔
      ∃ primitive : binaryHilbertFiniteValues (index := index) cusp level,
        DifferentiableOn ℝ (binaryAffineOrbitVector cusp basis primitive.val) UpperHalfPlane.upperHalfPlaneSet ∧
        (∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
          binaryHilbertOperator cusp basis matrix primitive.val = primitive.val) ∧
        binaryHolomorphicTangent cusp spherical basis level cycle =
          fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I 1 -
            Complex.I • fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I Complex.I := by
  constructor
  · intro zero
    obtain ⟨primitive, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp zero
    have potential : binaryUpperPotential cusp spherical basis level cycle =
        fun point => binaryAffineOrbitVector cusp basis primitive.val point - primitive.val := by
      funext point
      exact (congrArg Subtype.val (congrFun boundary (invertibleMatrix (binaryUpperSectionMatrix point)))).symm
    have primitive_regular : DifferentiableOn ℝ (binaryAffineOrbitVector cusp basis primitive.val) UpperHalfPlane.upperHalfPlaneSet := by
      apply (regular.add_const primitive.val).congr
      intro point _
      rw [potential]
      simp only [sub_add_cancel]
    refine ⟨primitive, primitive_regular, ?_, ?_⟩
    · intro matrix stabilizes
      have identity := congrArg Subtype.val (congrFun boundary matrix)
      change binaryHilbertOperator cusp basis matrix primitive.val - primitive.val =
        (cycle matrix : binaryHilbertFiniteValues cusp level).val at identity
      rw [stabilizer_zero matrix stabilizes] at identity
      exact sub_eq_zero.mp identity
    · have neighborhood := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp)
      have derivative := ((primitive_regular.differentiableAt neighborhood).hasFDerivAt.sub_const primitive.val).fderiv
      rw [binaryHolomorphicTangent, potential, derivative]
  · rintro ⟨primitive, primitive_regular, primitive_fixed, tangent⟩
    by_contra nonzero
    exact binaryHolomorphicTangent_not_coboundary cusp spherical basis level cycle nonzero regular
      stabilizer_zero primitive primitive_regular primitive_fixed tangent

end TernaryPeriodPolynomials.SphericalDetection.Helpers
