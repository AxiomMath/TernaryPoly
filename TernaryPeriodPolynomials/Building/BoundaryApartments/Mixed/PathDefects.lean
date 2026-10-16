module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.LeviCocycle

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

theorem pathDefect_radicalLevi_product
    (radical_first radical_second conjugate levi_first levi_second : rationalLevel)
    (first_left first_right second_left second_right conjugate_left conjugate_right : ℚ)
    (first_radical : radical_first.val = Adelic.lineUnipotent first_left first_right)
    (second_radical : radical_second.val = Adelic.lineUnipotent second_left second_right)
    (conjugate_radical : conjugate.val = Adelic.lineUnipotent conjugate_left conjugate_right)
    (first_line : levi_first.val ∈ Adelic.lineParabolic ℚ)
    (second_line : levi_second.val ∈ Adelic.lineParabolic ℚ)
    (first_block : levi_first.val.val 0 1 = 0 ∧ levi_first.val.val 0 2 = 0)
    (second_block : levi_second.val.val 0 1 = 0 ∧ levi_second.val.val 0 2 = 0)
    (conjugate_eq : levi_first * radical_second = conjugate * levi_first) :
    pathDefect specialPaths (radical_first * levi_first) (radical_second * levi_second) =
      translateChain radical_first.val
        (specialPaths levi_first - translateChain conjugate.val (specialPaths levi_first)) := by
  have product_eq : (radical_first * levi_first) * (radical_second * levi_second) =
      (radical_first * conjugate) * (levi_first * levi_second) := by
    calc
      (radical_first * levi_first) * (radical_second * levi_second) =
          radical_first * (levi_first * radical_second) * levi_second := by simp only [mul_assoc]
      _ = radical_first * (conjugate * levi_first) * levi_second := by rw [conjugate_eq]
      _ = (radical_first * conjugate) * (levi_first * levi_second) := by simp only [mul_assoc]
  have product_radical : (radical_first * conjugate).val =
      Adelic.lineUnipotent (first_left + conjugate_left) (first_right + conjugate_right) := by
    rw [Subgroup.coe_mul, first_radical, conjugate_radical, Adelic.lineUnipotent_add]
  rw [pathDefect, product_eq,
    specialPaths_radical_mul radical_first levi_first first_left first_right first_radical first_line,
    specialPaths_radical_mul radical_second levi_second second_left second_right second_radical second_line,
    specialPaths_radical_mul (radical_first * conjugate) (levi_first * levi_second)
      (first_left + conjugate_left) (first_right + conjugate_right) product_radical
      (Adelic.inLine_mul first_line second_line),
    specialPaths_levi_product levi_first levi_second first_line second_line first_block second_block]
  have commute : translateChain levi_first.val (translateChain radical_second.val
      (specialPaths levi_second)) =
        translateChain conjugate.val (translateChain levi_first.val (specialPaths levi_second)) := by
    rw [← translateChain_mul, ← translateChain_mul]
    have matrix_eq := congrArg Subtype.val conjugate_eq
    change levi_first.val * radical_second.val = conjugate.val * levi_first.val at matrix_eq
    rw [matrix_eq]
  simp only [Subgroup.coe_mul, translateChain_mul, map_add, map_sub]
  rw [commute]
  abel

theorem realizesPathClass_radicalLevi_product {degree : ℕ}
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (first_left first_right second_left second_right conjugate_left conjugate_right : ℤ)
    (levi_first levi_second : rationalLevel)
    (first_line : levi_first.val ∈ Adelic.lineParabolic ℚ)
    (second_line : levi_second.val ∈ Adelic.lineParabolic ℚ)
    (first_block : levi_first.val.val 0 1 = 0 ∧ levi_first.val.val 0 2 = 0)
    (second_block : levi_second.val.val 0 1 = 0 ∧ levi_second.val.val 0 2 = 0)
    (conjugate_eq : levi_first * integralRadical second_left second_right =
      integralRadical conjugate_left conjugate_right * levi_first) :
    cocycle.val.val ![1, (integralRadical first_left first_right * levi_first).val,
      ((integralRadical first_left first_right * levi_first) *
        (integralRadical second_left second_right * levi_second)).val] =
      -rationalCoefficientComponent degree trivialCharacter
        (integralRadical first_left first_right).val
        (functional (mixedRadicalChain levi_first conjugate_left conjugate_right)) := by
  have value := realizes 1 (integralRadical first_left first_right * levi_first)
    ((integralRadical first_left first_right * levi_first) *
      (integralRadical second_left second_right * levi_second))
  simp only [Subgroup.coe_one, inv_one, one_mul, inv_mul_cancel_left,
    map_one, Module.End.one_apply] at value
  change cocycle.val.val _ = functional (pathDefect specialPaths
    (integralRadical first_left first_right * levi_first)
    (integralRadical second_left second_right * levi_second)) at value
  rw [value, pathDefect_radicalLevi_product
    (integralRadical first_left first_right) (integralRadical second_left second_right)
    (integralRadical conjugate_left conjugate_right) levi_first levi_second
    (first_left : ℚ) (first_right : ℚ) (second_left : ℚ) (second_right : ℚ)
    (conjugate_left : ℚ) (conjugate_right : ℚ)
    (integralRadical_val _ _) (integralRadical_val _ _) (integralRadical_val _ _)
    first_line second_line first_block second_block conjugate_eq]
  have chain_eq : specialPaths levi_first -
      translateChain (integralRadical conjugate_left conjugate_right).val (specialPaths levi_first) =
        -mixedRadicalChain levi_first conjugate_left conjugate_right := by
    unfold mixedRadicalChain
    abel
  rw [chain_eq, map_neg, map_neg,
    functional_property.1 _ _
      (mixedRadicalChain_goodCycle levi_first first_line conjugate_left conjugate_right)]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
