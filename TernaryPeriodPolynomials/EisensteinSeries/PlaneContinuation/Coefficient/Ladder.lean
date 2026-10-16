module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ResonantCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLieAction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLadder

noncomputable def raising (data : CuspidalRepresentation) (degree : ℕ) : Module.End ℂ (Vectors data degree) :=
  operator data degree diagonalMatrix - Complex.I • operator data degree symmetricMatrix

noncomputable def lowering (data : CuspidalRepresentation) (degree : ℕ) : Module.End ℂ (Vectors data degree) :=
  operator data degree diagonalMatrix + Complex.I • operator data degree symmetricMatrix

theorem rotation_diagonal (data : CuspidalRepresentation) (degree : ℕ) :
    operator data degree rotationMatrix * operator data degree diagonalMatrix -
      operator data degree diagonalMatrix * operator data degree rotationMatrix = (2 : ℂ) • operator data degree symmetricMatrix := by
  rw [operator_commutator, rotation_diagonal_commutator, operator_real_smul]
  norm_num

theorem rotation_symmetric (data : CuspidalRepresentation) (degree : ℕ) :
    operator data degree rotationMatrix * operator data degree symmetricMatrix -
      operator data degree symmetricMatrix * operator data degree rotationMatrix = (-2 : ℂ) • operator data degree diagonalMatrix := by
  rw [operator_commutator, rotation_symmetric_commutator, operator_real_smul]
  norm_num

theorem rotation_raising (data : CuspidalRepresentation) (degree : ℕ) :
    operator data degree rotationMatrix * raising data degree - raising data degree * operator data degree rotationMatrix =
      (2 * Complex.I) • raising data degree := by
  calc
    _ = (operator data degree rotationMatrix * operator data degree diagonalMatrix -
          operator data degree diagonalMatrix * operator data degree rotationMatrix) -
        Complex.I • (operator data degree rotationMatrix * operator data degree symmetricMatrix -
          operator data degree symmetricMatrix * operator data degree rotationMatrix) := by
      simp only [raising, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    _ = _ := by
      rw [rotation_diagonal, rotation_symmetric]
      simp only [raising, smul_sub, smul_smul, mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
      module

theorem rotation_lowering (data : CuspidalRepresentation) (degree : ℕ) :
    operator data degree rotationMatrix * lowering data degree - lowering data degree * operator data degree rotationMatrix =
      (-2 * Complex.I) • lowering data degree := by
  calc
    _ = (operator data degree rotationMatrix * operator data degree diagonalMatrix -
          operator data degree diagonalMatrix * operator data degree rotationMatrix) +
        Complex.I • (operator data degree rotationMatrix * operator data degree symmetricMatrix -
          operator data degree symmetricMatrix * operator data degree rotationMatrix) := by
      simp only [lowering, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    _ = _ := by
      rw [rotation_diagonal, rotation_symmetric]
      simp only [lowering, smul_add, smul_smul, mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
      module

theorem raising_zero_weight (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (eigen : operator data degree rotationMatrix vectors = 0) :
    CoefficientRotation.shifted data degree 2 (raising data degree vectors) = 0 := by
  have equality := congrArg (fun linear : Module.End ℂ (Vectors data degree) => linear vectors) (rotation_raising data degree)
  change operator data degree rotationMatrix (raising data degree vectors) -
    raising data degree (operator data degree rotationMatrix vectors) = (2 * Complex.I) • raising data degree vectors at equality
  rw [eigen, map_zero, sub_zero] at equality
  change operator data degree rotationMatrix (raising data degree vectors) -
    (Complex.I * (2 : ℤ)) • raising data degree vectors = 0
  rw [equality]
  norm_num [mul_comm Complex.I]

theorem lowering_zero_weight (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (eigen : operator data degree rotationMatrix vectors = 0) :
    CoefficientRotation.shifted data degree (-2) (lowering data degree vectors) = 0 := by
  have equality := congrArg (fun linear : Module.End ℂ (Vectors data degree) => linear vectors) (rotation_lowering data degree)
  change operator data degree rotationMatrix (lowering data degree vectors) -
    lowering data degree (operator data degree rotationMatrix vectors) = (-2 * Complex.I) • lowering data degree vectors at equality
  rw [eigen, map_zero, sub_zero] at equality
  change operator data degree rotationMatrix (lowering data degree vectors) -
    (Complex.I * (-2 : ℤ)) • lowering data degree vectors = 0
  rw [equality]
  norm_num [mul_comm Complex.I]

theorem cocycle_raising (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first)) :
    CoefficientRotation.shifted data degree 2 (differential diagonalMatrix - Complex.I • differential symmetricMatrix) =
      raising data degree (differential rotationMatrix) := by
  have firstEquation := equation rotationMatrix diagonalMatrix
  have secondEquation := equation rotationMatrix symmetricMatrix
  rw [rotation_diagonal_commutator, map_smul] at firstEquation
  rw [rotation_symmetric_commutator, map_smul, neg_smul] at secondEquation
  change operator data degree rotationMatrix (differential diagonalMatrix) -
    operator data degree diagonalMatrix (differential rotationMatrix) = (2 : ℂ) • differential symmetricMatrix at firstEquation
  change operator data degree rotationMatrix (differential symmetricMatrix) -
    operator data degree symmetricMatrix (differential rotationMatrix) = -((2 : ℂ) • differential diagonalMatrix) at secondEquation
  rw [sub_eq_iff_eq_add] at firstEquation secondEquation
  simp only [CoefficientRotation.shifted, raising, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul]
  rw [firstEquation, secondEquation]
  norm_num only [Int.cast_ofNat]
  simp only [smul_add, smul_sub, smul_neg, smul_smul, ← mul_assoc, Complex.I_mul_I]
  module

theorem cocycle_lowering (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first)) :
    CoefficientRotation.shifted data degree (-2) (differential diagonalMatrix + Complex.I • differential symmetricMatrix) =
      lowering data degree (differential rotationMatrix) := by
  have firstEquation := equation rotationMatrix diagonalMatrix
  have secondEquation := equation rotationMatrix symmetricMatrix
  rw [rotation_diagonal_commutator, map_smul] at firstEquation
  rw [rotation_symmetric_commutator, map_smul, neg_smul] at secondEquation
  change operator data degree rotationMatrix (differential diagonalMatrix) -
    operator data degree diagonalMatrix (differential rotationMatrix) = (2 : ℂ) • differential symmetricMatrix at firstEquation
  change operator data degree rotationMatrix (differential symmetricMatrix) -
    operator data degree symmetricMatrix (differential rotationMatrix) = -((2 : ℂ) • differential diagonalMatrix) at secondEquation
  rw [sub_eq_iff_eq_add] at firstEquation secondEquation
  simp only [CoefficientRotation.shifted, lowering, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, map_add, map_smul]
  rw [firstEquation, secondEquation]
  norm_num only [Int.cast_neg, Int.cast_ofNat]
  simp only [smul_add, smul_sub, smul_neg, smul_smul, ← mul_assoc, Complex.I_mul_I]
  module

/-- The resonant rotation value of a Lie cocycle is annihilated by both ladder operators. -/
theorem resonant_value_ladders (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (eigen : operator data degree rotationMatrix (differential rotationMatrix) = 0) :
    raising data degree (differential rotationMatrix) = 0 ∧ lowering data degree (differential rotationMatrix) = 0 := by
  constructor
  · exact CoefficientRotation.shifted_range_eigen_zero data degree 2 _ _
      (cocycle_raising data degree differential equation) (raising_zero_weight data degree _ eigen)
  · exact CoefficientRotation.shifted_range_eigen_zero data degree (-2) _ _
      (cocycle_lowering data degree differential equation) (lowering_zero_weight data degree _ eigen)

theorem resonant_value_invariant (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (eigen : operator data degree rotationMatrix (differential rotationMatrix) = 0) :
    operator data degree diagonalMatrix (differential rotationMatrix) = 0 ∧
      operator data degree symmetricMatrix (differential rotationMatrix) = 0 := by
  obtain ⟨raisingZero, loweringZero⟩ := resonant_value_ladders data degree differential equation eigen
  have first : (2 : ℂ) • operator data degree diagonalMatrix (differential rotationMatrix) = 0 := by
    calc
      _ = raising data degree (differential rotationMatrix) + lowering data degree (differential rotationMatrix) := by
        simp only [raising, lowering, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
        module
      _ = 0 := by rw [raisingZero, loweringZero, add_zero]
  have second : (2 * Complex.I) • operator data degree symmetricMatrix (differential rotationMatrix) = 0 := by
    calc
      _ = lowering data degree (differential rotationMatrix) - raising data degree (differential rotationMatrix) := by
        simp only [raising, lowering, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
        module
      _ = 0 := by rw [raisingZero, loweringZero, sub_zero]
  exact ⟨(smul_eq_zero.mp first).resolve_left (by norm_num), (smul_eq_zero.mp second).resolve_left (by norm_num)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLadder
