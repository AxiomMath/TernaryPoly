module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviMatrices

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem radicalRepresentation_binary (degree : ℕ) (radical : Multiplicative (ℤ × ℤ))
    (polynomial : Binary.HomogeneousPoly degree) :
    radicalRepresentation degree radical (binaryHomogeneousEmbedding degree polynomial) =
      binaryHomogeneousEmbedding degree polynomial := by
  change rationalCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (Int.castRingHom ℚ)
      (lineUnipotent radical.toAdd.1 radical.toAdd.2)) _ = _
  rw [map_lineUnipotent]
  exact binaryHomogeneousEmbedding_lineUnipotent degree _ _ polynomial

def binaryPairRadicalCocycle (degree : ℕ)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    crossedCocycles (radicalRepresentation degree) :=
  ⟨fun radical => (radical.toAdd.1 : ℂ) • binaryHomogeneousEmbedding degree pair.1 +
    (radical.toAdd.2 : ℂ) • binaryHomogeneousEmbedding degree pair.2, by
    intro first second
    change ((first.toAdd.1 + second.toAdd.1 : ℤ) : ℂ) •
        binaryHomogeneousEmbedding degree pair.1 +
      ((first.toAdd.2 + second.toAdd.2 : ℤ) : ℂ) •
        binaryHomogeneousEmbedding degree pair.2 =
      ((first.toAdd.1 : ℂ) • binaryHomogeneousEmbedding degree pair.1 +
        (first.toAdd.2 : ℂ) • binaryHomogeneousEmbedding degree pair.2) +
      radicalRepresentation degree first
        ((second.toAdd.1 : ℂ) • binaryHomogeneousEmbedding degree pair.1 +
          (second.toAdd.2 : ℂ) • binaryHomogeneousEmbedding degree pair.2)
    rw [Int.cast_add, Int.cast_add, add_smul, add_smul, map_add, map_smul, map_smul,
      radicalRepresentation_binary, radicalRepresentation_binary]
    exact add_add_add_comm _ _ _ _⟩

theorem binaryPairRadicalCocycle_generator (degree : ℕ)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) (index : Fin 2) :
    (binaryPairRadicalCocycle degree pair).val (integralRadicalGenerator index) =
      binaryHomogeneousEmbedding degree (if index = 0 then pair.1 else pair.2) := by
  fin_cases index <;> simp [binaryPairRadicalCocycle, integralRadicalGenerator]

theorem finiteExponentialRatio_fixed_of_zero {Value : Type} [AddCommGroup Value]
    [Module ℂ Value] [Module ℚ Value] [IsScalarTower ℚ ℂ Value] [SMulCommClass ℚ ℂ Value]
    (bound : ℕ) (operator : Module.End ℂ Value) (value : Value) (zero : operator value = 0) :
    finiteExponentialRatio bound operator value = value := by
  have powerZero : ∀ order : ℕ, (operator ^ (order + 1)) value = 0 := by
    intro order
    rw [pow_succ, Module.End.mul_apply, zero, map_zero]
  simp [finiteExponentialRatio, Finset.sum_range_succ', LinearMap.sum_apply,
    LinearMap.smul_apply, powerZero]

theorem radicalInfinitesimal_binary (degree : ℕ) (positive : 0 < degree) (index : Fin 2)
    (polynomial : Binary.HomogeneousPoly degree) :
    radicalInfinitesimal degree positive index (binaryHomogeneousEmbedding degree polynomial) = 0 := by
  apply Subtype.ext
  change X index.succ * pderiv 0 (binaryPolynomialEmbedding polynomial.val) = 0
  rw [(pderiv_zero_iff_binary _).mpr ⟨polynomial.val, rfl⟩, mul_zero]

theorem radicalDifferenceNormalization_binary (degree : ℕ) (positive : 0 < degree) (index : Fin 2)
    (polynomial : Binary.HomogeneousPoly degree) :
    radicalDifferenceNormalization degree positive index (binaryHomogeneousEmbedding degree polynomial) =
      binaryHomogeneousEmbedding degree polynomial := by
  unfold radicalDifferenceNormalization
  apply (finiteExponentialRatioEquiv degree (-(radicalInfinitesimal degree positive index))
    (radicalInfinitesimal_nilpotent degree positive index).neg).injective
  rw [LinearEquiv.apply_symm_apply, finiteExponentialRatioEquiv_apply]
  symm
  apply finiteExponentialRatio_fixed_of_zero
  rw [LinearMap.neg_apply, radicalInfinitesimal_binary, neg_zero]

theorem radicalKoszulBinaryEquiv_embedding (degree : ℕ) (positive : 0 < degree)
    (cycle : radicalKoszulCycles degree positive) :
    binaryHomogeneousEmbedding (degree + 1)
      (radicalKoszulBinaryEquiv degree positive
        ((radicalKoszulBoundaries degree positive).mkQ cycle)) =
      radicalKoszulProjection degree cycle.val := by
  have equality : binaryDerivativeKernelEquiv (degree + 1)
      (radicalKoszulBinaryEquiv degree positive
        ((radicalKoszulBoundaries degree positive).mkQ cycle)) =
      radicalKoszulCycleProjection degree positive cycle :=
    (binaryDerivativeKernelEquiv (degree + 1)).apply_symm_apply _
  exact congrArg Subtype.val equality

theorem radicalCrossedBinaryEquiv_embedding (degree : ℕ) (positive : 0 < degree)
    (cochain : crossedCocycles (radicalRepresentation degree)) :
    binaryHomogeneousEmbedding (degree + 1)
      (radicalCrossedBinaryEquiv degree positive
        ((radicalCrossedBoundaries degree).mkQ cochain)) =
      radicalKoszulProjection degree
        (radicalPairNormalization degree positive (radicalCrossedEvaluation degree cochain).val) := by
  exact radicalKoszulBinaryEquiv_embedding degree positive
    (discreteRadicalCycleEquiv degree positive (radicalCrossedEvaluation degree cochain))

def binaryPairWedge (degree : ℕ)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    Binary.HomogeneousPoly (degree + 1) :=
  ⟨X 0 * pair.2.val - X 1 * pair.1.val, by
    have order : 1 + degree = degree + 1 := by omega
    exact order ▸ ((isHomogeneous_X ℂ (0 : Fin 2)).mul pair.2.property).sub
      ((isHomogeneous_X ℂ (1 : Fin 2)).mul pair.1.property)⟩

theorem binaryPairRadicalCocycle_coordinate (degree : ℕ) (positive : 0 < degree)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    radicalCrossedBinaryEquiv degree positive
      ((radicalCrossedBoundaries degree).mkQ (binaryPairRadicalCocycle degree pair)) =
        binaryPairWedge degree pair := by
  apply binaryHomogeneousEmbedding_injective (degree + 1)
  rw [radicalCrossedBinaryEquiv_embedding]
  have pairEquality : radicalPairNormalization degree positive
      (radicalCrossedEvaluation degree (binaryPairRadicalCocycle degree pair)).val =
      (binaryHomogeneousEmbedding degree pair.1, binaryHomogeneousEmbedding degree pair.2) := by
    apply Prod.ext
    · change radicalDifferenceNormalization degree positive 0
        ((binaryPairRadicalCocycle degree pair).val (integralRadicalGenerator 0)) = _
      rw [binaryPairRadicalCocycle_generator, ite_eq_left rfl, radicalDifferenceNormalization_binary]
    · change radicalDifferenceNormalization degree positive 1
        ((binaryPairRadicalCocycle degree pair).val (integralRadicalGenerator 1)) = _
      rw [binaryPairRadicalCocycle_generator, ite_eq_right (by decide), radicalDifferenceNormalization_binary]
  rw [pairEquality]
  apply Subtype.ext
  simp [radicalKoszulProjection, binaryPairWedge, binaryHomogeneousEmbedding,
    binaryPolynomialEmbedding]

def binaryEulerPair (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree :=
  (-((degree + 1 : ℕ) : ℂ)⁻¹ •
      ⟨pderiv 1 polynomial.val, by simpa using polynomial.property.pderiv (i := (1 : Fin 2))⟩,
    ((degree + 1 : ℕ) : ℂ)⁻¹ •
      ⟨pderiv 0 polynomial.val, by simpa using polynomial.property.pderiv (i := (0 : Fin 2))⟩)

theorem binaryPairWedge_euler (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    binaryPairWedge degree (binaryEulerPair degree polynomial) = polynomial := by
  apply Subtype.ext
  have euler := polynomial.property.sum_X_mul_pderiv
  have scalarEuler : X 0 * pderiv 0 polynomial.val + X 1 * pderiv 1 polynomial.val =
      ((degree + 1 : ℕ) : ℂ) • polynomial.val := by
    simpa only [Fin.sum_univ_two, Nat.cast_smul_eq_nsmul] using euler
  change X 0 * (((degree + 1 : ℕ) : ℂ)⁻¹ • pderiv 0 polynomial.val) -
    X 1 * (-((degree + 1 : ℕ) : ℂ)⁻¹ • pderiv 1 polynomial.val) = polynomial.val
  rw [mul_smul_comm, mul_smul_comm, neg_smul, sub_neg_eq_add, ← smul_add, scalarEuler, smul_smul]
  have nonzero : ((degree + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
  rw [inv_mul_cancel₀ nonzero, one_smul]

theorem radicalCrossedH1_binaryPair_representative (degree : ℕ) (positive : 0 < degree)
    (coordinate : RadicalCrossedH1 degree) :
    ∃ pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree,
      (radicalCrossedBoundaries degree).mkQ (binaryPairRadicalCocycle degree pair) = coordinate := by
  refine ⟨binaryEulerPair degree (radicalCrossedBinaryEquiv degree positive coordinate), ?_⟩
  apply (radicalCrossedBinaryEquiv degree positive).injective
  rw [binaryPairRadicalCocycle_coordinate, binaryPairWedge_euler]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
