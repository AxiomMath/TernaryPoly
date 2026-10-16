module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Center

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RelativeCocycle

theorem central_value_zero {degree : ℕ} (data : InducingData degree)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data.cusp degree)
    (equation : ∀ first second, operator data.cusp degree first (differential second) -
      operator data.cusp degree second (differential first) = differential (first * second - second * first)) :
    differential 1 = 0 := by
  apply CoefficientInvariants.eq_zero_of_invariant data.cusp degree (differential 1)
  · simpa only [CoefficientCenter.operator_identity data, LinearMap.zero_apply, sub_zero, mul_one, one_mul,
      sub_self, map_zero] using equation diagonalMatrix 1
  · simpa only [CoefficientCenter.operator_identity data, LinearMap.zero_apply, sub_zero, mul_one, one_mul,
      sub_self, map_zero] using equation rotationMatrix 1

theorem resonant_rotation_zero (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (eigen : operator data degree rotationMatrix (differential rotationMatrix) = 0) :
    differential rotationMatrix = 0 :=
  CoefficientInvariants.eq_zero_of_invariant data degree (differential rotationMatrix)
    (CoefficientLadder.resonant_value_invariant data degree differential equation eigen).1 eigen

/-- Nontrivial relative cohomology is obtained from the actual supplied group cohomology. -/
theorem exists_relative_cocycle {degree : ℕ} (data : InducingData degree) :
    ∃ differential : BinaryMatrix →ₗ[ℝ] Vectors data.cusp degree,
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ direction index,
          (differential direction index).val ∈ fixedSubspace data.cusp level) ∧
      (∀ first second, operator data.cusp degree first (differential second) -
        operator data.cusp degree second (differential first) = differential (first * second - second * first)) ∧
      differential 1 = 0 ∧ differential rotationMatrix = 0 ∧
      ¬ ∃ vectors : Vectors data.cusp degree, ∀ direction,
        differential direction = operator data.cusp degree direction vectors := by
  obtain ⟨differential, fixed, equation, eigen, nontrivialClass⟩ := ResonantCocycle.exists_resonant_cocycle data
  exact ⟨differential, fixed, equation, central_value_zero data differential equation,
    resonant_rotation_zero data.cusp degree differential equation eigen, nontrivialClass⟩

theorem raising_value_eigen (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (relative : differential rotationMatrix = 0) :
    CoefficientRotation.shifted data degree 2 (differential diagonalMatrix - Complex.I • differential symmetricMatrix) = 0 := by
  rw [CoefficientLadder.cocycle_raising data degree differential equation, relative, map_zero]

theorem lowering_value_eigen (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (relative : differential rotationMatrix = 0) :
    CoefficientRotation.shifted data degree (-2) (differential diagonalMatrix + Complex.I • differential symmetricMatrix) = 0 := by
  rw [CoefficientLadder.cocycle_lowering data degree differential equation, relative, map_zero]

/-- The two relative components satisfy the remaining Lie cocycle equation. -/
theorem ladder_relation (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (relative : differential rotationMatrix = 0) :
    CoefficientLadder.lowering data degree (differential diagonalMatrix - Complex.I • differential symmetricMatrix) =
      CoefficientLadder.raising data degree (differential diagonalMatrix + Complex.I • differential symmetricMatrix) := by
  have equality := equation diagonalMatrix symmetricMatrix
  rw [diagonal_symmetric_commutator, map_smul, relative, smul_zero] at equality
  have commutation := sub_eq_zero.mp equality
  simp only [CoefficientLadder.raising, CoefficientLadder.lowering, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [commutation]
  module

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RelativeCocycle
