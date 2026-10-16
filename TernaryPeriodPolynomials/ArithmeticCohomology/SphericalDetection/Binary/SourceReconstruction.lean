module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointReconstruction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binarySmoothValues_eq_single_zero (cusp : CuspidalRepresentation) (degree : ℕ)
    (lower : binarySmoothValues cusp (Fin (degree + 2)))
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0) :
    binarySmoothValues_val cusp lower = Pi.single 0 (lower 0).val := by
  funext position
  refine Fin.cases ?_ (fun position => ?_) position
  · change (lower 0).val = (Pi.single 0 (lower 0).val : Fin (degree + 2) → cusp.H) 0
    rw [Pi.single_eq_same]
  · change (lower position.succ).val = _
    simp [support, Fin.succ_ne_zero]

/-- The actual normal cycle is the explicit integral attached to its actual first endpoint. -/
theorem binaryNormalCycle_eq_endpointPrimitive (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree)
    (cohomological : Cohomological cusp degree) (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁
      (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (central_zero : ∀ unit : ℝˣ, 0 < unit.val →
      cycle (Matrix.GeneralLinearGroup.scalar (Fin 2) unit) = 0)
    (lower : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_value : binarySmoothValues_val cusp lower =
      binaryHolomorphicTangent cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0)
    (matrix : BinaryRealGL) :
    (cycle matrix : binaryHilbertFiniteValues cusp level).val =
      binaryEndpointPrimitive cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 (lower 0).val)
        ((matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
  have reflection_zero := binaryRelativeCycle_reflection_zero cusp spherical odd cohomological
    level cycle rotations_zero
  have stabilizer_zero := binary_cocycle_stabilizer_zero _ cycle rotations_zero reflection_zero central_zero
  rw [binaryRelativeCycle_eq_endpointPrimitive cusp spherical (binaryWeightBasis (degree + 1))
    level cycle regular stabilizer_zero, ← lower_value, binarySmoothValues_eq_single_zero cusp degree lower support]

/-- Reconstruction before normalization retains exactly the supplied Hilbert coboundary. -/
theorem binarySourceCycle_reconstruction (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree)
    (cohomological : Cohomological cusp degree) (level : Subgroup BinaryFiniteGL)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (correction : binaryHilbertFiniteValues (index := Fin (degree + 2)) cusp level)
    (cycle : groupCohomology.cocycles₁
      (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level))
    (formula : ∀ matrix : BinaryRealGL, (cycle matrix : binaryHilbertFiniteValues cusp level).val =
      binaryHilbertEmbedding cusp (binaryWeightBasis (degree + 1)) (original matrix) -
        (binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) matrix correction.val - correction.val))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (central_zero : ∀ unit : ℝˣ, 0 < unit.val →
      cycle (Matrix.GeneralLinearGroup.scalar (Fin 2) unit) = 0)
    (lower : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_value : binarySmoothValues_val cusp lower =
      binaryHolomorphicTangent cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0)
    (matrix : BinaryRealGL) :
    binaryHilbertEmbedding cusp (binaryWeightBasis (degree + 1)) (original matrix) =
      binaryEndpointPrimitive cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 (lower 0).val)
        ((matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
      (binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) matrix correction.val - correction.val) := by
  rw [← binaryNormalCycle_eq_endpointPrimitive cusp spherical odd cohomological level cycle
    regular rotations_zero central_zero lower lower_value support matrix, formula, sub_add_cancel]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
