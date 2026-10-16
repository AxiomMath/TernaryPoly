module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Binary

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

def mixedRadicalChain (levi : rationalLevel) (first second : ℤ) : EdgeChains :=
  translateChain (integralRadical first second).val (specialPaths levi) - specialPaths levi

theorem mixedRadicalChain_goodCycle (levi : rationalLevel)
    (levi_line : levi.val ∈ Adelic.lineParabolic ℚ) (first second : ℤ) :
    GoodCycle (mixedRadicalChain levi first second) := by
  obtain ⟨left, right, conjugate_eq⟩ := integralRadical_conjugate_coordinates
    levi first second levi_line
  have conjugate_path := specialPaths_radical _ _ _ conjugate_eq
  have product_path := specialPaths_radical_mul _ _ _ _
    (integralRadical_val first second) levi_line
  have product : levi * (levi⁻¹ * integralRadical first second * levi) =
      integralRadical first second * levi := by simp [mul_assoc]
  have defect : pathDefect specialPaths levi (levi⁻¹ * integralRadical first second * levi) =
      -mixedRadicalChain levi first second := by
    simp only [pathDefect, product, conjugate_path, map_zero, add_zero, product_path,
      mixedRadicalChain, neg_sub]
  have cycle := pathDefect_goodCycle specialPaths_isPathFamily
    levi (levi⁻¹ * integralRadical first second * levi)
  rw [defect] at cycle
  constructor
  · have boundary := congrArg Neg.neg cycle.1
    simpa only [map_neg, neg_neg, neg_zero] using boundary
  · simpa only [zero_sub, neg_neg] using goodChain_sub goodChain_zero cycle.2

theorem mixedRadicalChain_add (levi : rationalLevel) (first second third fourth : ℤ) :
    mixedRadicalChain levi (first + third) (second + fourth) =
      translateChain (integralRadical first second).val (mixedRadicalChain levi third fourth) +
        mixedRadicalChain levi first second := by
  simp only [mixedRadicalChain, ← integralRadical_mul, Subgroup.coe_mul,
    translateChain_mul, map_sub]
  abel

theorem mixedRadicalChain_commuting (levi : rationalLevel) (first second third fourth : ℤ) :
    translateChain (integralRadical first second).val (mixedRadicalChain levi third fourth) -
      mixedRadicalChain levi third fourth =
    translateChain (integralRadical third fourth).val (mixedRadicalChain levi first second) -
      mixedRadicalChain levi first second := by
  have first_sum := mixedRadicalChain_add levi first second third fourth
  have second_sum := mixedRadicalChain_add levi third fourth first second
  rw [add_comm third first, add_comm fourth second] at second_sum
  rw [first_sum] at second_sum
  have rearranged := congrArg (fun chain : EdgeChains => chain -
    mixedRadicalChain levi first second - mixedRadicalChain levi third fourth) second_sum
  exact (by abel : _ = _).trans (rearranged.trans (by abel))

theorem mixedRadicalValue_pair_relation {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    (levi : rationalLevel) (levi_line : levi.val ∈ Adelic.lineParabolic ℚ) :
    radicalTranslation degree 1 (functional (mixedRadicalChain levi 0 1)) -
      functional (mixedRadicalChain levi 0 1) =
    radicalTranslation degree 2 (functional (mixedRadicalChain levi 1 0)) -
      functional (mixedRadicalChain levi 1 0) := by
  have first := functional_property.1 (integralRadical 1 0)
    (mixedRadicalChain levi 0 1) (mixedRadicalChain_goodCycle levi levi_line 0 1)
  have second := functional_property.1 (integralRadical 0 1)
    (mixedRadicalChain levi 1 0) (mixedRadicalChain_goodCycle levi levi_line 1 0)
  simp only [integralRadical_val, Int.cast_one, Int.cast_zero,
    rationalCoefficient_firstRadical, rationalCoefficient_secondRadical] at first second
  rw [← first, ← second, ← map_sub, ← map_sub]
  exact congrArg functional (by
    simpa only [integralRadical_val, Int.cast_one, Int.cast_zero] using
      mixedRadicalChain_commuting levi 1 0 0 1)

theorem mixedBernoulliCoordinate_binary {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (levi : rationalLevel) (levi_line : levi.val ∈ Adelic.lineParabolic ℚ) :
    pderiv 0 (mixedBernoulliCoordinate cocycle levi.val) = 0 := by
  have first := mixedBarEdge_of_levi realizes levi 1 0 levi_line
  have second := mixedBarEdge_of_levi realizes levi 0 1 levi_line
  simp only [Int.cast_one, Int.cast_zero] at first second
  have first_value : mixedBarEdge cocycle levi.val (Adelic.lineUnipotent 1 0) =
      -(functional (mixedRadicalChain levi 1 0)).val := by
    simpa only [mixedRadicalChain, integralRadical_val, Int.cast_one, Int.cast_zero] using first
  have second_value : mixedBarEdge cocycle levi.val (Adelic.lineUnipotent 0 1) =
      -(functional (mixedRadicalChain levi 0 1)).val := by
    simpa only [mixedRadicalChain, integralRadical_val, Int.cast_one, Int.cast_zero] using second
  have pair := mixedRadicalValue_pair_relation functional_property levi levi_line
  have binary := radicalCocycle_contraction_binary degree
    (functional (mixedRadicalChain levi 1 0)) (functional (mixedRadicalChain levi 0 1)) pair
  have signs (left right : Poly) : -left - -right = -(left - right) := by ring
  rw [mixedBernoulliCoordinate, first_value, second_value, bernoulliOperator_neg,
    bernoulliOperator_neg, mul_neg, mul_neg, signs]
  rw [map_neg, binary, neg_zero]

theorem bernoulliObstruction_binary {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    pderiv 0 (bernoulliObstruction polynomial) = 0 := by
  have binary := mixedBernoulliCoordinate_binary functional_property
    (pathCocycle_realizes functional_property specialPaths_isPathFamily) arithmeticBinaryA
    (by rw [arithmeticBinaryA_val]; exact ⟨rfl, rfl⟩)
  rw [arithmeticBinaryA_val, mixedBernoulliCoordinate_binaryA functional_property
    (pathCocycle_realizes functional_property specialPaths_isPathFamily), map_neg] at binary
  exact neg_eq_zero.mp binary

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
