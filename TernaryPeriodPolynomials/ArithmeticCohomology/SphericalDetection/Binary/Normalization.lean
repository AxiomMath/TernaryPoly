module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DifferentiableCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CocycleLocalRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

/-- Rotation averaging of the supplied cycle, with its original finite level. -/
def binaryRotationFiniteCycle (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix) :
    groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level) :=
  ⟨fun matrix => ⟨binaryRotationNormalizedCycle cusp basis original matrix,
    fun element position => binaryRotationNormalizedCycle_finiteLevel cusp basis original continuous level fixed
      element matrix position⟩, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    apply Subtype.ext
    exact (binaryRotationNormalizedCycle_cocycle cusp spherical basis original first second).trans (add_comm _ _)⟩

/-- The actual cycle normalized at the orthogonal stabilizer. -/
def binarySymmetricNormalizedCycle (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix) :
    groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level) :=
  binaryReflectionNormalizedCycle cusp spherical basis level
    (binaryRotationFiniteCycle cusp spherical basis original continuous level fixed)

theorem binarySymmetricNormalizedCycle_formula (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix)
    (matrix : BinaryRealGL) :
    (binarySymmetricNormalizedCycle cusp spherical basis original continuous level fixed matrix :
      binaryHilbertFiniteValues cusp level).val =
      binaryHilbertEmbedding cusp basis (original matrix) -
        (binaryHilbertOperator cusp basis matrix
          (binaryRotationPrimitive cusp basis original +
            (-(2 : ℂ)⁻¹) • binaryRotationNormalizedCycle cusp basis original UpperHalfPlane.J) -
          (binaryRotationPrimitive cusp basis original +
            (-(2 : ℂ)⁻¹) • binaryRotationNormalizedCycle cusp basis original UpperHalfPlane.J)) := by
  change binaryRotationNormalizedCycle cusp basis original matrix -
    (binaryHilbertOperator cusp basis matrix
      ((-(2 : ℂ)⁻¹) • binaryRotationNormalizedCycle cusp basis original UpperHalfPlane.J) -
      (-(2 : ℂ)⁻¹) • binaryRotationNormalizedCycle cusp basis original UpperHalfPlane.J) = _
  rw [binaryRotationNormalizedCycle, map_add]
  abel

theorem binarySymmetricNormalizedCycle_finite_boundary (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix) :
    ∃ primitive : binaryHilbertFiniteValues (index := index) cusp level,
      ∀ matrix : BinaryRealGL,
        (binarySymmetricNormalizedCycle cusp spherical basis original continuous level fixed matrix :
          binaryHilbertFiniteValues cusp level).val =
          binaryHilbertEmbedding cusp basis (original matrix) -
            (binaryHilbertOperator cusp basis matrix primitive.val - primitive.val) := by
  refine ⟨⟨binaryRotationPrimitive cusp basis original +
    (-(2 : ℂ)⁻¹) • binaryRotationNormalizedCycle cusp basis original UpperHalfPlane.J, ?_⟩, ?_⟩
  · intro element position
    simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul,
      binaryRotationPrimitive_finiteLevel cusp basis original continuous level fixed,
      binaryRotationNormalizedCycle_finiteLevel cusp basis original continuous level fixed]
  · exact binarySymmetricNormalizedCycle_formula cusp spherical basis original continuous level fixed

theorem binarySymmetricNormalizedCycle_zero_detects (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (regular : Smooth (fun point : Fin 1 → BinaryRealGL => binaryHilbertEmbedding cusp basis (original (point 0))))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix)
    (zero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
      (binarySymmetricNormalizedCycle cusp spherical basis original continuous level fixed) = 0) :
    groupCohomology.H1π (binaryCuspidalRep cusp degree) original = 0 := by
  by_contra nonzero
  rw [binarySymmetricNormalizedCycle, binaryReflectionNormalizedCycle_H1] at zero
  obtain ⟨primitive, boundary⟩ := (groupCohomology.H1π_eq_zero_iff _).mp zero
  apply binaryRotationNormalizedCycle_no_finiteLevel_primitive cusp basis original nonzero
    continuous regular level level_open level_compact fixed
  refine ⟨primitive.val, ?_, primitive.property⟩
  intro matrix
  exact (congrArg Subtype.val (congrFun boundary matrix)).symm

theorem binarySymmetricNormalizedCycle_continuous (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix) :
    Continuous (fun matrix =>
      (binarySymmetricNormalizedCycle cusp spherical basis original continuous level fixed matrix :
        binaryHilbertFiniteValues cusp level).val) :=
  binaryReflectionNormalizedCycle_continuous cusp spherical basis level _
    (binaryRotationNormalizedCycle_continuous cusp basis original continuous)

theorem binarySymmetricNormalizedCycle_contDiffOn (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (regular : Smooth (fun point : Fin 1 → BinaryRealGL => binaryHilbertEmbedding cusp basis (original (point 0))))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun matrix : BinaryRealMatrix =>
      (binarySymmetricNormalizedCycle cusp spherical basis original continuous level fixed (invertibleMatrix matrix) :
        binaryHilbertFiniteValues cusp level).val) {matrix | matrix.det ≠ 0} :=
  binaryCocycleShift_contDiffOn _ (binaryRotationFiniteCycle cusp spherical basis original continuous level fixed)
    (binaryHilbertFiniteValues cusp level).subtype
    (binaryRotationNormalizedCycle_contDiffOn cusp basis original regular) UpperHalfPlane.J (-(2 : ℂ)⁻¹)

theorem binarySymmetricNormalizedCycle_stabilizer_zero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (original matrix)))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix) :
    ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I →
      binarySymmetricNormalizedCycle cusp spherical basis original continuous level fixed matrix = 0 := by
  apply binary_cocycle_stabilizer_zero
  · apply binaryReflectionNormalizedCycle_rotation
    intro angle
    apply Subtype.ext
    exact binaryRotationNormalizedCycle_rotation cusp basis original continuous angle
  · exact binaryReflectionNormalizedCycle_reflection cusp spherical basis level _
  · exact binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical cohomological basis level level_open level_compact _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
