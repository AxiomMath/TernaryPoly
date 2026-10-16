module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RelativeCoboundary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialWeights
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointPair

noncomputable def remainder (data : CuspidalRepresentation) (degree : ℕ) (first second : Vectors data degree) : Vectors data degree :=
  second - CoefficientLadder.lowering data degree (TriangularPrimitive.primitive data degree first)

theorem remainder_eigen (data : CuspidalRepresentation) (degree : ℕ) (first second : Vectors data degree)
    (firstEigen : CoefficientRotation.shifted data degree 2 first = 0)
    (secondEigen : CoefficientRotation.shifted data degree (-2) second = 0) :
    CoefficientRotation.shifted data degree (-2) (remainder data degree first second) = 0 := by
  rw [remainder, map_sub, secondEigen, CoefficientLadder.lowering_zero_weight data degree _
    (TriangularPrimitive.primitive_eigen data degree first firstEigen), sub_zero]

theorem endpoint_equation (data : CuspidalRepresentation) (degree : ℕ) (first second : Vectors data degree)
    (firstEigen : CoefficientRotation.shifted data degree 2 first = 0)
    (equation : CoefficientLadder.lowering data degree first = CoefficientLadder.raising data degree second) :
    CoefficientLadder.raising data degree (remainder data degree first second) =
      basisVector data degree (degree + 1) (LieOperators.lowering data (TriangularPrimitive.endpoint data degree first)) := by
  have equality := RelativeCoboundary.residual_equation data degree first second
    (TriangularPrimitive.primitive data degree first) equation (TriangularPrimitive.primitive_eigen data degree first firstEigen)
  change CoefficientLadder.lowering data degree (TriangularPrimitive.residual data degree first) =
    CoefficientLadder.raising data degree (remainder data degree first second) at equality
  rw [TriangularPrimitive.residual_basis, MonomialLadder.lowering_basis_last] at equality
  exact equality.symm

theorem remainder_fixed (data : CuspidalRepresentation) (degree : ℕ) (first second : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (fixed : ∀ index,
      (first index).val ∈ fixedSubspace data level ∧ (second index).val ∈ fixedSubspace data level)
    (index : Index (degree + 1)) : (remainder data degree first second index).val ∈ fixedSubspace data level :=
  (fixedSubspace data level).sub_mem (fixed index).2 (RelativeCoboundary.lowering_fixed data degree
    (TriangularPrimitive.primitive data degree first) level
    (TriangularPrimitive.primitive_fixed data degree first level (fun other => (fixed other).1)) index)

theorem endpoint_fixed (data : CuspidalRepresentation) (degree : ℕ) (first : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (fixed : ∀ index, (first index).val ∈ fixedSubspace data level) :
    (TriangularPrimitive.endpoint data degree first).val ∈ fixedSubspace data level := by
  apply component_fixed data degree (degree + 1) (TriangularPrimitive.residual data degree first) level
  intro index
  exact (fixedSubspace data level).sub_mem (fixed index) (RelativeCoboundary.raising_fixed data degree
    (TriangularPrimitive.primitive data degree first) level (TriangularPrimitive.primitive_fixed data degree first level fixed) index)

/-- The raising half of a nontrivial relative pair can be concentrated at the top monomial. -/
theorem exists_endpoint_pair {degree : ℕ} (data : InducingData degree) :
    ∃ endpoint : data.cusp.smooth, ∃ remaining : Vectors data.cusp degree,
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ endpoint.val ∈ fixedSubspace data.cusp level ∧
          ∀ index, (remaining index).val ∈ fixedSubspace data.cusp level) ∧
      rotationOperator data.cusp endpoint = (Complex.I * (degree + 3 : ℤ)) • endpoint ∧
      CoefficientRotation.shifted data.cusp degree (-2) remaining = 0 ∧
      CoefficientLadder.raising data.cusp degree remaining =
        basisVector data.cusp degree (degree + 1) (LieOperators.lowering data.cusp endpoint) ∧
      ¬ ∃ vectors : Vectors data.cusp degree, operator data.cusp degree rotationMatrix vectors = 0 ∧
        basisVector data.cusp degree (degree + 1) endpoint = CoefficientLadder.raising data.cusp degree vectors ∧
          remaining = CoefficientLadder.lowering data.cusp degree vectors := by
  obtain ⟨first, second, ⟨level, openness, compactness, fixed⟩, firstEigen, secondEigen, equation, nontrivialClass⟩ :=
    RelativePair.exists_nontrivial_relative_pair data
  refine ⟨TriangularPrimitive.endpoint data.cusp degree first, remainder data.cusp degree first second,
    ⟨level, openness, compactness, endpoint_fixed data.cusp degree first level (fun index => (fixed index).1),
      remainder_fixed data.cusp degree first second level fixed⟩,
    TriangularPrimitive.endpoint_eigen data.cusp degree first firstEigen,
    remainder_eigen data.cusp degree first second firstEigen secondEigen,
    endpoint_equation data.cusp degree first second firstEigen equation, ?_⟩
  have notExact := RelativeCoboundary.residual_not_exact data.cusp degree first second
    (TriangularPrimitive.primitive data.cusp degree first) nontrivialClass (TriangularPrimitive.primitive_eigen data.cusp degree first firstEigen)
  change ¬ ∃ vectors, operator data.cusp degree rotationMatrix vectors = 0 ∧
    TriangularPrimitive.residual data.cusp degree first = CoefficientLadder.raising data.cusp degree vectors ∧
      remainder data.cusp degree first second = CoefficientLadder.lowering data.cusp degree vectors at notExact
  rw [TriangularPrimitive.residual_basis] at notExact
  exact notExact

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointPair
