module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.FrameCancellations

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous MvPolynomial

theorem derivative_iterate_neg (iterations : ℕ) (polynomial : Poly) :
    ((fun value : Poly => pderiv 0 value)^[iterations]) (-polynomial) =
      -(((fun value : Poly => pderiv 0 value)^[iterations]) polynomial) := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', induction_hypothesis]
    exact map_neg _ _

theorem bernoulliOperator_neg (degree : ℕ) (parameter polynomial : Poly) :
    bernoulliOperator degree parameter (-polynomial) =
      -bernoulliOperator degree parameter polynomial := by
  simp [bernoulliOperator, Finset.sum_neg_distrib]

theorem mixedBarEdge_of_levi {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (levi : rationalLevel) (first second : ℤ)
    (levi_line : levi.val ∈ Adelic.lineParabolic ℚ) :
    mixedBarEdge cocycle levi.val (Adelic.lineUnipotent (first : ℚ) (second : ℚ)) =
      -(functional (translateChain (Adelic.lineUnipotent (first : ℚ) (second : ℚ))
        (specialPaths levi) - specialPaths levi)).val := by
  obtain ⟨left, right, conjugate_eq⟩ := integralRadical_conjugate_coordinates levi first second levi_line
  simpa only [integralRadical_val] using mixedBarEdge_of_specialPaths realizes
    levi (integralRadical first second)
    (specialPaths_radical _ _ _ (integralRadical_val _ _))
    (specialPaths_radical _ _ _ conjugate_eq)
    (specialPaths_radical_mul _ _ _ _ (integralRadical_val _ _) levi_line)

theorem mixedBarEdge_binaryA_first {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBarEdge cocycle binaryA (Adelic.lineUnipotent 1 0) =
      -(bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val) := by
  have value := mixedBarEdge_of_levi realizes arithmeticBinaryA 1 0
    (by rw [arithmeticBinaryA_val]; exact ⟨rfl,rfl⟩)
  simp only [arithmeticBinaryA_val, Int.cast_one, Int.cast_zero,
    specialPaths_binaryA] at value
  change mixedBarEdge cocycle binaryA (Adelic.lineUnipotent 1 0) =
    -(functional (translateChain (Adelic.lineUnipotent 1 0) binaryAPath - binaryAPath)).val
    at value
  rw [value, firstRadical_frameCancellation]
  exact congrArg Neg.neg (firstBernoulliFrame_evaluation functional_property)

theorem mixedBarEdge_binaryA_second {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBarEdge cocycle binaryA (Adelic.lineUnipotent 0 1) =
      -(bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val -
        bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] polynomial.val +
        bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] polynomial.val) := by
  have value := mixedBarEdge_of_levi realizes arithmeticBinaryA 0 1
    (by rw [arithmeticBinaryA_val]; exact ⟨rfl,rfl⟩)
  simp only [arithmeticBinaryA_val, Int.cast_one, Int.cast_zero,
    specialPaths_binaryA] at value
  change mixedBarEdge cocycle binaryA (Adelic.lineUnipotent 0 1) =
    -(functional (translateChain (Adelic.lineUnipotent 0 1) binaryAPath - binaryAPath)).val
    at value
  rw [value, secondRadical_frameCancellation]
  simp only [map_add, Submodule.coe_add, firstFrame, secondFrame, thirdFrame,
    firstBernoulliFrame_evaluation functional_property,
    secondBernoulliFrame_evaluation functional_property,
    thirdBernoulliFrame_evaluation functional_property, sub_eq_add_neg]

theorem mixedBernoulliCoordinate_binaryA {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBernoulliCoordinate cocycle binaryA = -bernoulliObstruction polynomial := by
  rw [mixedBernoulliCoordinate, mixedBarEdge_binaryA_first functional_property realizes,
    mixedBarEdge_binaryA_second functional_property realizes]
  simp only [bernoulliOperator_neg, bernoulliObstruction]
  ring

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
