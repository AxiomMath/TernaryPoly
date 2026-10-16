module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Cochains

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

theorem realizesPathClass_inhomogeneous {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {paths : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional paths cocycle)
    (first second : rationalLevel) :
    cocycle.val.val ![1, first.val, (first * second).val] =
      functional (pathDefect paths first second) := by
  have value := realizes 1 first (first * second)
  simpa only [Subgroup.coe_one, inv_one, one_mul, inv_mul_cancel_left,
    map_one, Module.End.one_apply, pathDefect] using value

theorem mixedBarEdge_of_specialPaths {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {paths : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional paths cocycle)
    (levi radical : rationalLevel)
    (radical_path : paths radical = 0)
    (conjugate_path : paths (levi⁻¹ * radical * levi) = 0)
    (product_path : paths (radical * levi) = translateChain radical.val (paths levi)) :
    mixedBarEdge cocycle levi.val radical.val =
      -(functional (translateChain radical.val (paths levi) - paths levi)).val := by
  have first_value := realizesPathClass_inhomogeneous realizes levi (levi⁻¹ * radical * levi)
  have second_value := realizesPathClass_inhomogeneous realizes radical levi
  have product_eq : levi * (levi⁻¹ * radical * levi) = radical * levi := by
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  rw [product_eq] at first_value
  change (cocycle.val.val ![1, levi.val, (radical * levi).val]).val -
    (cocycle.val.val ![1, radical.val, (radical * levi).val]).val = _
  rw [first_value, second_value]
  simp only [pathDefect, product_eq, radical_path, conjugate_path, product_path,
    map_zero, add_zero, zero_add, sub_self, map_sub]
  change (functional (paths levi)).val -
      (functional (translateChain radical.val (paths levi))).val - 0 =
    -((functional (translateChain radical.val (paths levi))).val -
      (functional (paths levi)).val)
  abel

theorem mixedBarEdge_zero_of_specialPaths {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {paths : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional paths cocycle)
    (levi radical : rationalLevel)
    (radical_path : paths radical = 0)
    (conjugate_path : paths (levi⁻¹ * radical * levi) = 0)
    (product_path : paths (radical * levi) = translateChain radical.val (paths levi))
    (levi_path : paths levi = 0) : mixedBarEdge cocycle levi.val radical.val = 0 := by
  rw [mixedBarEdge_of_specialPaths realizes levi radical radical_path conjugate_path product_path,
    levi_path, map_zero, sub_self, map_zero]
  exact neg_zero

theorem realizesPathClass_pureRadical {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {paths : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional paths cocycle)
    (first second : rationalLevel) (first_path : paths first = 0)
    (second_path : paths second = 0) (product_path : paths (first * second) = 0) :
    cocycle.val.val ![1, first.val, (first * second).val] = 0 := by
  rw [realizesPathClass_inhomogeneous realizes]
  simp [pathDefect, first_path, second_path, product_path]

theorem realizesPathClass_pureLevi {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {paths : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional paths cocycle)
    (first second : rationalLevel) (chain : EdgeChains)
    (first_path : paths first = chain - translateChain first.val chain)
    (second_path : paths second = chain - translateChain second.val chain)
    (product_path : paths (first * second) = chain - translateChain (first * second).val chain) :
    cocycle.val.val ![1, first.val, (first * second).val] = 0 := by
  rw [realizesPathClass_inhomogeneous realizes]
  have defect_zero : pathDefect paths first second = 0 := by
    simp only [pathDefect, first_path, second_path, product_path, map_sub,
      ← translateChain_mul, Subgroup.coe_mul]
    abel
  rw [defect_zero, map_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
