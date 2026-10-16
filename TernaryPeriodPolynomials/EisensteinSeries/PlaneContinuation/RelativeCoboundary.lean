module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.TriangularPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLadder
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RelativeCoboundary

theorem diagonal_symmetric (data : CuspidalRepresentation) (degree : ℕ) :
    operator data degree diagonalMatrix * operator data degree symmetricMatrix -
      operator data degree symmetricMatrix * operator data degree diagonalMatrix = (-2 : ℂ) • operator data degree rotationMatrix := by
  rw [CoefficientLieAction.operator_commutator, diagonal_symmetric_commutator, operator_real_smul]
  norm_num

theorem lowering_raising (data : CuspidalRepresentation) (degree : ℕ) :
    CoefficientLadder.lowering data degree * CoefficientLadder.raising data degree -
      CoefficientLadder.raising data degree * CoefficientLadder.lowering data degree =
        (4 * Complex.I) • operator data degree rotationMatrix := by
  calc
    _ = (-2 * Complex.I) • (operator data degree diagonalMatrix * operator data degree symmetricMatrix -
        operator data degree symmetricMatrix * operator data degree diagonalMatrix) := by
      simp only [CoefficientLadder.lowering, CoefficientLadder.raising, add_mul, sub_mul, mul_add, mul_sub,
        smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
      module
    _ = _ := by
      rw [diagonal_symmetric, smul_smul]
      congr 1
      ring

theorem commute_on_invariant (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (invariant : operator data degree rotationMatrix vectors = 0) :
    CoefficientLadder.lowering data degree (CoefficientLadder.raising data degree vectors) =
      CoefficientLadder.raising data degree (CoefficientLadder.lowering data degree vectors) := by
  have equality := congrArg (fun linear : Module.End ℂ (Vectors data degree) => linear vectors) (lowering_raising data degree)
  change CoefficientLadder.lowering data degree (CoefficientLadder.raising data degree vectors) -
      CoefficientLadder.raising data degree (CoefficientLadder.lowering data degree vectors) =
        (4 * Complex.I) • operator data degree rotationMatrix vectors at equality
  rw [invariant, smul_zero] at equality
  exact sub_eq_zero.mp equality

theorem residual_equation (data : CuspidalRepresentation) (degree : ℕ) (first second vectors : Vectors data degree)
    (equation : CoefficientLadder.lowering data degree first = CoefficientLadder.raising data degree second)
    (invariant : operator data degree rotationMatrix vectors = 0) :
    CoefficientLadder.lowering data degree (first - CoefficientLadder.raising data degree vectors) =
      CoefficientLadder.raising data degree (second - CoefficientLadder.lowering data degree vectors) := by
  rw [map_sub, map_sub, equation, commute_on_invariant data degree vectors invariant]

theorem residual_not_exact (data : CuspidalRepresentation) (degree : ℕ) (first second vectors : Vectors data degree)
    (nontrivialClass : ¬ ∃ primitive : Vectors data degree, operator data degree rotationMatrix primitive = 0 ∧
      first = CoefficientLadder.raising data degree primitive ∧ second = CoefficientLadder.lowering data degree primitive)
    (invariant : operator data degree rotationMatrix vectors = 0) :
    ¬ ∃ primitive : Vectors data degree, operator data degree rotationMatrix primitive = 0 ∧
      first - CoefficientLadder.raising data degree vectors = CoefficientLadder.raising data degree primitive ∧
        second - CoefficientLadder.lowering data degree vectors = CoefficientLadder.lowering data degree primitive := by
  rintro ⟨primitive, primitiveInvariant, firstEquation, secondEquation⟩
  apply nontrivialClass
  refine ⟨primitive + vectors, ?_, ?_, ?_⟩
  · rw [map_add, primitiveInvariant, invariant, add_zero]
  · rw [map_add]
    exact sub_eq_iff_eq_add.mp firstEquation
  · rw [map_add]
    exact sub_eq_iff_eq_add.mp secondEquation

theorem raising_fixed (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (fixed : ∀ index, (vectors index).val ∈ fixedSubspace data level)
    (index : Index (degree + 1)) : (CoefficientLadder.raising data degree vectors index).val ∈ fixedSubspace data level :=
  (fixedSubspace data level).sub_mem (operator_preserves_fixed data degree level diagonalMatrix vectors fixed index)
    ((fixedSubspace data level).smul_mem Complex.I (operator_preserves_fixed data degree level symmetricMatrix vectors fixed index))

theorem lowering_fixed (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (fixed : ∀ index, (vectors index).val ∈ fixedSubspace data level)
    (index : Index (degree + 1)) : (CoefficientLadder.lowering data degree vectors index).val ∈ fixedSubspace data level :=
  (fixedSubspace data level).add_mem (operator_preserves_fixed data degree level diagonalMatrix vectors fixed index)
    ((fixedSubspace data level).smul_mem Complex.I (operator_preserves_fixed data degree level symmetricMatrix vectors fixed index))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RelativeCoboundary
