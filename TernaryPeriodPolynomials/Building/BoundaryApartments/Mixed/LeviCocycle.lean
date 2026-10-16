module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.RadicalExactness

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem rationalLevi_product_block (first second : rationalLevel)
    (first_block : first.val.val 0 1 = 0 ∧ first.val.val 0 2 = 0)
    (second_block : second.val.val 0 1 = 0 ∧ second.val.val 0 2 = 0) :
    (first * second).val.val 0 1 = 0 ∧ (first * second).val.val 0 2 = 0 := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three,
    first_block.1, first_block.2, second_block.1, second_block.2]

theorem specialPaths_levi_product (first second : rationalLevel)
    (first_line : first.val ∈ Adelic.lineParabolic ℚ)
    (second_line : second.val ∈ Adelic.lineParabolic ℚ)
    (first_block : first.val.val 0 1 = 0 ∧ first.val.val 0 2 = 0)
    (second_block : second.val.val 0 1 = 0 ∧ second.val.val 0 2 = 0) :
    specialPaths (first * second) =
      specialPaths first + translateChain first.val (specialPaths second) := by
  rw [specialPaths_levi (first * second) (Adelic.inLine_mul first_line second_line)
    (rationalLevi_product_block first second first_block second_block),
    specialPaths_levi first first_line first_block,
    specialPaths_levi second second_line second_block, map_sub]
  simp only [Subgroup.coe_mul, translateChain_mul]
  abel

theorem mixedRadicalChain_levi_product (first second : rationalLevel)
    (first_line : first.val ∈ Adelic.lineParabolic ℚ)
    (second_line : second.val ∈ Adelic.lineParabolic ℚ)
    (first_block : first.val.val 0 1 = 0 ∧ first.val.val 0 2 = 0)
    (second_block : second.val.val 0 1 = 0 ∧ second.val.val 0 2 = 0)
    (left right conjugate_left conjugate_right : ℤ)
    (conjugate : first⁻¹ * integralRadical left right * first =
      integralRadical conjugate_left conjugate_right) :
    mixedRadicalChain (first * second) left right =
      mixedRadicalChain first left right +
        translateChain first.val (mixedRadicalChain second conjugate_left conjugate_right) := by
  have commute : (integralRadical left right).val * first.val =
      first.val * (integralRadical conjugate_left conjugate_right).val := by
    rw [← conjugate]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  unfold mixedRadicalChain
  rw [specialPaths_levi_product first second first_line second_line first_block second_block,
    map_add, map_sub]
  rw [← translateChain_mul, commute, translateChain_mul]
  abel

theorem mixedRadicalValue_levi_product {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    (first second : rationalLevel)
    (first_line : first.val ∈ Adelic.lineParabolic ℚ)
    (second_line : second.val ∈ Adelic.lineParabolic ℚ)
    (first_block : first.val.val 0 1 = 0 ∧ first.val.val 0 2 = 0)
    (second_block : second.val.val 0 1 = 0 ∧ second.val.val 0 2 = 0)
    (left right conjugate_left conjugate_right : ℤ)
    (conjugate : first⁻¹ * integralRadical left right * first =
      integralRadical conjugate_left conjugate_right) :
    functional (mixedRadicalChain (first * second) left right) =
      functional (mixedRadicalChain first left right) +
        rationalCoefficientComponent degree trivialCharacter first.val
          (functional (mixedRadicalChain second conjugate_left conjugate_right)) := by
  rw [mixedRadicalChain_levi_product first second first_line second_line first_block
    second_block left right conjugate_left conjugate_right conjugate, map_add,
    functional_property.1 first _
      (mixedRadicalChain_goodCycle second second_line conjugate_left conjugate_right)]

theorem mixedBarEdge_levi_product {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (first second : rationalLevel)
    (first_line : first.val ∈ Adelic.lineParabolic ℚ)
    (second_line : second.val ∈ Adelic.lineParabolic ℚ)
    (first_block : first.val.val 0 1 = 0 ∧ first.val.val 0 2 = 0)
    (second_block : second.val.val 0 1 = 0 ∧ second.val.val 0 2 = 0)
    (left right conjugate_left conjugate_right : ℤ)
    (conjugate : first⁻¹ * integralRadical left right * first =
      integralRadical conjugate_left conjugate_right) :
    mixedBarEdge cocycle (first * second).val
        (Adelic.lineUnipotent (left : ℚ) (right : ℚ)) =
      mixedBarEdge cocycle first.val (Adelic.lineUnipotent (left : ℚ) (right : ℚ)) -
        (rationalCoefficientComponent degree trivialCharacter first.val
          (functional (mixedRadicalChain second conjugate_left conjugate_right))).val := by
  rw [mixedBarEdge_of_levi realizes (first * second) left right
    (Adelic.inLine_mul first_line second_line), mixedBarEdge_of_levi realizes first left right first_line]
  rw [← integralRadical_val left right]
  change -(functional (mixedRadicalChain (first * second) left right)).val =
    -(functional (mixedRadicalChain first left right)).val -
      (rationalCoefficientComponent degree trivialCharacter first.val
        (functional (mixedRadicalChain second conjugate_left conjugate_right))).val
  rw [mixedRadicalValue_levi_product functional_property first second first_line second_line
    first_block second_block left right conjugate_left conjugate_right conjugate,
    Submodule.coe_add]
  ring

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
