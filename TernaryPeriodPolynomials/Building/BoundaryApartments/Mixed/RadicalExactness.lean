module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Exactness

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous MvPolynomial

theorem mixedRadicalValue_crossed {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    (levi : rationalLevel) (levi_line : levi.val ∈ Adelic.lineParabolic ℚ)
    (first second third fourth : ℤ) :
    functional (mixedRadicalChain levi (first + third) (second + fourth)) =
      rationalCoefficientComponent degree trivialCharacter
        (integralRadical first second).val
          (functional (mixedRadicalChain levi third fourth)) +
      functional (mixedRadicalChain levi first second) := by
  rw [mixedRadicalChain_add, map_add,
    functional_property.1 _ _ (mixedRadicalChain_goodCycle levi levi_line third fourth)]

theorem mixedBernoulliCoordinate_zero_exists_radicalPrimitive {degree : ℕ}
    {polynomial : HomogeneousPoly degree} (degree_positive : 0 < degree)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (levi : rationalLevel) (levi_line : levi.val ∈ Adelic.lineParabolic ℚ)
    (coordinate_zero : mixedBernoulliCoordinate cocycle levi.val = 0) :
    ∃ primitive : HomogeneousPoly degree, ∀ first second : ℤ,
      mixedBarEdge cocycle levi.val (Adelic.lineUnipotent (first : ℚ) (second : ℚ)) =
        (rationalCoefficientComponent degree trivialCharacter
          (Adelic.lineUnipotent (first : ℚ) (second : ℚ)) primitive).val - primitive.val := by
  have first := mixedBarEdge_of_levi realizes levi 1 0 levi_line
  have second := mixedBarEdge_of_levi realizes levi 0 1 levi_line
  simp only [Int.cast_one, Int.cast_zero] at first second
  have contraction_zero : X 2 * bernoulliOperator degree (X 1)
        (functional (mixedRadicalChain levi 1 0)).val -
      X 1 * bernoulliOperator degree (X 2)
        (functional (mixedRadicalChain levi 0 1)).val = 0 := by
    rw [mixedBernoulliCoordinate, first, second] at coordinate_zero
    simp only [bernoulliOperator_neg] at coordinate_zero
    have chain_first : translateChain (Adelic.lineUnipotent 1 0) (specialPaths levi) -
        specialPaths levi = mixedRadicalChain levi 1 0 := by
      simp only [mixedRadicalChain, integralRadical_val, Int.cast_one, Int.cast_zero]
    have chain_second : translateChain (Adelic.lineUnipotent 0 1) (specialPaths levi) -
        specialPaths levi = mixedRadicalChain levi 0 1 := by
      simp only [mixedRadicalChain, integralRadical_val, Int.cast_one, Int.cast_zero]
    rw [chain_first, chain_second] at coordinate_zero
    linear_combination -coordinate_zero
  obtain ⟨primitive, primitive_eq⟩ := radicalCrossed_zero_exists_primitive degree_positive
    (fun first second => functional (mixedRadicalChain levi first second))
    (mixedRadicalValue_crossed functional_property levi levi_line) contraction_zero
  refine ⟨-primitive, ?_⟩
  intro first second
  rw [mixedBarEdge_of_levi realizes levi first second levi_line]
  rw [← integralRadical_val first second]
  change -(functional (mixedRadicalChain levi first second)).val = _
  rw [primitive_eq, map_neg]
  simp only [Submodule.coe_sub, Submodule.coe_neg, integralRadical_val]
  ring

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
