module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.SpecialPaths
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.Edge

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix

theorem integralImage_mul (first second : IntegralGL3)
    (first_arithmetic : first ∈ arithmeticLevel)
    (second_arithmetic : second ∈ arithmeticLevel) :
    integralImage first first_arithmetic * integralImage second second_arithmetic =
      integralImage (first * second) (arithmeticLevel.mul_mem first_arithmetic second_arithmetic) := by
  apply Subtype.ext
  exact (map_mul (GeneralLinearGroup.map (Int.castRingHom ℚ)) first second).symm

theorem badLineLevi_mul {first second : IntegralGL3}
    (first_levi : BadLineLevi first) (second_levi : BadLineLevi second) :
    BadLineLevi (first * second) := by
  refine ⟨arithmeticLevel.mul_mem first_levi.1 second_levi.1, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, first_levi.2.1, first_levi.2.2.1,
      first_levi.2.2.2.1, first_levi.2.2.2.2, second_levi.2.1, second_levi.2.2.1,
      second_levi.2.2.2.1, second_levi.2.2.2.2]

theorem specialPaths_integralLevi (matrix : IntegralGL3) (matrix_levi : BadLineLevi matrix) :
    specialPaths (integralImage matrix matrix_levi.1) = connectingChain -
      translateChain (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) connectingChain := by
  apply specialPaths_levi
  · constructor
    · change (matrix.val 1 0 : ℚ) = 0
      rw [matrix_levi.2.2.2.1]
      rfl
    · change (matrix.val 2 0 : ℚ) = 0
      rw [matrix_levi.2.2.2.2]
      rfl
  · constructor
    · change (matrix.val 0 1 : ℚ) = 0
      rw [matrix_levi.2.1]
      rfl
    · change (matrix.val 0 2 : ℚ) = 0
      rw [matrix_levi.2.2.1]
      rfl

theorem specialPaths_pureMixed {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) : PureMixedBadLine cocycle := by
  constructor
  · intro first second third fourth
    have first_path := specialPaths_radical (integralRadical first second) (first : ℚ) (second : ℚ)
      (integralRadical_val first second)
    have second_path := specialPaths_radical (integralRadical third fourth) (third : ℚ) (fourth : ℚ)
      (integralRadical_val third fourth)
    have product_path : specialPaths (integralRadical first second * integralRadical third fourth) = 0 := by
      rw [integralRadical_mul]
      exact specialPaths_radical _ _ _ (integralRadical_val _ _)
    have value := realizesPathClass_pureRadical realizes
      (integralRadical first second) (integralRadical third fourth) first_path second_path product_path
    simpa only [Subgroup.coe_mul, integralRadical_val] using value
  · intro first second first_levi second_levi
    have product_levi := badLineLevi_mul first_levi second_levi
    have product_path : specialPaths
        (integralImage first first_levi.1 * integralImage second second_levi.1) =
        connectingChain - translateChain
          (integralImage first first_levi.1 * integralImage second second_levi.1).val connectingChain := by
      rw [integralImage_mul]
      exact specialPaths_integralLevi (first * second) product_levi
    have value := realizesPathClass_pureLevi realizes
      (integralImage first first_levi.1) (integralImage second second_levi.1) connectingChain
      (specialPaths_integralLevi first first_levi) (specialPaths_integralLevi second second_levi) product_path
    simpa only [Subgroup.coe_mul, integralImage, map_mul] using value

theorem specialPathCocycle_pureMixed {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    PureMixedBadLine (pathCocycle functional_property specialPaths_isPathFamily) :=
  specialPaths_pureMixed (pathCocycle_realizes functional_property specialPaths_isPathFamily)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
