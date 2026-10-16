module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Normalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.NormalForm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A normal form for the given analytic cycle, preserving an explicit finite-level correction
and a detection implication for its original cusp-valued cohomology class. -/
theorem binaryCocycle_exists_detecting_normal_form (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      binaryHilbertEmbedding cusp (binaryWeightBasis (degree + 1)) (original (invertibleMatrix matrix))) 1)
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (original matrix) = original matrix) :
    ∃ (correction : binaryHilbertFiniteValues (index := Fin (degree + 2)) cusp level)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level))
      (lower upper : binarySmoothValues cusp (Fin (degree + 2))),
      (∀ matrix : BinaryRealGL, (cycle matrix : binaryHilbertFiniteValues cusp level).val =
        binaryHilbertEmbedding cusp (binaryWeightBasis (degree + 1)) (original matrix) -
          (binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) matrix correction.val - correction.val)) ∧
      (groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level) cycle = 0 →
        groupCohomology.H1π (binaryCuspidalRep cusp degree) original = 0) ∧
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
      (∀ position : Fin (degree + 1), lower position.succ = 0) := by
  let basis := binaryWeightBasis (degree + 1)
  have continuous := binaryHilbertCocycle_continuous_of_analyticAt_one cusp basis original analytic
  have regular := binaryHilbertCocycle_smooth_of_analyticAt_one cusp basis original analytic
  let symmetric := binarySymmetricNormalizedCycle cusp spherical basis original continuous level fixed
  have symmetric_regular := binaryUpperPotential_contDiffOn cusp spherical basis level symmetric
    (binarySymmetricNormalizedCycle_contDiffOn cusp spherical basis original continuous regular level fixed)
  have stabilizer_zero := binarySymmetricNormalizedCycle_stabilizer_zero cusp spherical cohomological basis
    original continuous level level_open level_compact fixed
  obtain ⟨normal_primitive, cycle, lower, upper, cycle_shift, same_class, cycle_regular, rotations_zero,
    central_zero, lower_mem, upper_mem, lower_value, upper_value, closed, support⟩ :=
    binaryFiniteCycle_exists_relative_normal_form cusp spherical cohomological level level_open level_compact
      symmetric symmetric_regular stabilizer_zero
  obtain ⟨symmetric_primitive, symmetric_boundary⟩ :=
    binarySymmetricNormalizedCycle_finite_boundary cusp spherical basis original continuous level fixed
  refine ⟨normal_primitive + symmetric_primitive, cycle, lower, upper, ?_, ?_, cycle_regular,
    rotations_zero, central_zero, lower_mem, upper_mem, lower_value, upper_value, closed, support⟩
  · intro matrix
    rw [cycle_shift]
    change (symmetric matrix : binaryHilbertFiniteValues cusp level).val -
      (binaryHilbertOperator cusp basis matrix normal_primitive.val - normal_primitive.val) =
      binaryHilbertEmbedding cusp basis (original matrix) -
        (binaryHilbertOperator cusp basis matrix (normal_primitive.val + symmetric_primitive.val) -
          (normal_primitive.val + symmetric_primitive.val))
    rw [symmetric_boundary, map_add]
    abel
  · intro zero
    apply binarySymmetricNormalizedCycle_zero_detects cusp spherical basis original continuous regular
      level level_open level_compact fixed
    exact same_class.symm.trans zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
