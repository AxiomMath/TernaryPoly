module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalLeviCocycles

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryHomogeneousRestrict_realLevi (degree : ℕ) (matrix : BinaryRealGL)
    (polynomial : HomogeneousPoly degree) :
    binaryHomogeneousRestrict degree
        (realCoefficientComponent degree trivialCharacter (planeLevi matrix 1) polynomial) =
      Binary.homogeneousAction degree (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)
        (binaryHomogeneousRestrict degree polynomial) := by
  rw [realCoefficientComponent_trivial, map_planeLevi_one]
  apply Subtype.ext
  change binaryPolynomialRestrict (action (-1)
    (planeLevi (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) 1) polynomial.val) = _
  rw [action_apply, planeLevi_determinantCharacter, planeLevi_inverse, map_smul]
  simp only [Units.val_one, one_zpow, mul_one, planeLevi_value]
  rw [restrict_substitute_planeBlock]
  rfl

theorem binaryPairContraction_equivariant (exponent : ℤ) (matrix : Binary.GL2)
    (pair : Fin 2 → Binary.Poly) :
    X 0 * (matrix⁻¹.val 0 0 • Binary.action exponent matrix (pair 0) +
      matrix⁻¹.val 1 0 • Binary.action exponent matrix (pair 1)) +
    X 1 * (matrix⁻¹.val 0 1 • Binary.action exponent matrix (pair 0) +
      matrix⁻¹.val 1 1 • Binary.action exponent matrix (pair 1)) =
      Binary.action exponent matrix (X 0 * pair 0 + X 1 * pair 1) := by
  simp only [Binary.action_apply, map_add, map_mul, Binary.substitute_X,
    Binary.linearForm, Fin.sum_univ_two, smul_eq_C_mul]
  ring

theorem realUpperCuspidalCocycleLevi_projectedAxis {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (matrix : BinaryRealGL) (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0)
    (coordinate : Fin 2) (argument : BinaryAdelicGL) :
    binaryPolynomialRestrict
        ((realUpperCuspidalCocycleLevi degree cusp matrix cycle (realRadicalAxis coordinate 1)).val argument).val =
      normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
        Binary.action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)
          ((matrix⁻¹.val 0 coordinate : ℂ) •
              binaryPolynomialRestrict ((cycle (realRadicalAxis 0 1)).val (argument * atInfinity matrix)).val +
            (matrix⁻¹.val 1 coordinate : ℂ) •
              binaryPolynomialRestrict ((cycle (realRadicalAxis 1 1)).val (argument * atInfinity matrix)).val) := by
  have equality : binaryHomogeneousRestrict degree
      ((realUpperCuspidalCocycleLevi degree cusp matrix cycle (realRadicalAxis coordinate 1)).val argument) =
      normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
        Binary.homogeneousAction degree (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)
          ((matrix⁻¹.val 0 coordinate : ℂ) •
              binaryHomogeneousRestrict degree ((cycle (realRadicalAxis 0 1)).val (argument * atInfinity matrix)) +
            (matrix⁻¹.val 1 coordinate : ℂ) •
              binaryHomogeneousRestrict degree ((cycle (realRadicalAxis 1 1)).val (argument * atInfinity matrix))) := by
    rw [realUpperCuspidalCocycleLevi_apply, map_smul, binaryHomogeneousRestrict_realLevi,
      realUpperProjectedCocycle_value degree cusp basis cycle regular,
      realRadicalInverseLevi_axis, realRadicalInverseLevi_axis]
  exact congrArg Subtype.val equality

theorem realUpperCuspidalBinaryCoordinate_equivariant {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (matrix : BinaryRealGL) (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0) :
    (realUpperCuspidalBinaryCoordinate degree cusp (realUpperCuspidalCocycleLevi degree cusp matrix cycle)).val =
      binaryCohomologicalAction degree matrix (realUpperCuspidalBinaryCoordinate degree cusp cycle).val := by
  funext argument
  apply Subtype.ext
  rw [realUpperCuspidalBinaryCoordinate_value,
    realUpperCuspidalCocycleLevi_projectedAxis degree cusp basis matrix cycle regular,
    realUpperCuspidalCocycleLevi_projectedAxis degree cusp basis matrix cycle regular]
  change _ = normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
    Binary.action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)
      ((realUpperCuspidalBinaryCoordinate degree cusp cycle).val (argument * atInfinity matrix)).val
  rw [realUpperCuspidalBinaryCoordinate_value, map_smul]
  have contraction := binaryPairContraction_equivariant (-1)
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)
    (fun coordinate => binaryPolynomialRestrict
      ((cycle (realRadicalAxis coordinate 1)).val (argument * atInfinity matrix)).val)
  rw [← map_inv] at contraction
  simp only [map_add, map_smul, mul_smul_comm, ← smul_add]
  rw [smul_comm]
  congr 1
  congr 1
  simpa only [map_add, GeneralLinearGroup.map_apply, Complex.coe_algebraMap] using contraction

end TernaryPeriodPolynomials.SphericalDetection.Helpers
