module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section MixedCocycles

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def barValue (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (c : cocycles Γ ρ) (first second : G) : V :=
  c.val.val ![1, first, first * second]

theorem barValue_cocycle (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (c : cocycles Γ ρ) (first : Γ) (second third : G) :
    ρ first.val (barValue Γ ρ c second third) -
      barValue Γ ρ c (first.val * second) third +
      barValue Γ ρ c first.val (second * third) -
      barValue Γ ρ c first.val second = 0 := by
  have relation := cocycle_four_vertices Γ ρ c
    1 first.val (first.val * second) (first.val * second * third)
  have equivariance := c.val.property first ![1, second, second * third]
  have vertices_eq : (fun index => first.val * ![1, second, second * third] index) =
      ![first.val, first.val * second, first.val * second * third] := by
    funext index
    fin_cases index
    · exact mul_one first.val
    · rfl
    · exact (mul_assoc first.val second third).symm
  rw [vertices_eq] at equivariance
  rw [equivariance] at relation
  simpa only [barValue, mul_assoc] using relation

def mixedValue (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (c : cocycles Γ ρ) (levi radical : G) : V :=
  barValue Γ ρ c levi (levi⁻¹ * radical * levi) -
    barValue Γ ρ c radical levi

theorem mixedValue_radical_cocycle (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (c : cocycles Γ ρ)
    (levi first : Γ) (second : G)
    (pure : barValue Γ ρ c first.val second = 0)
    (conjugate_pure : barValue Γ ρ c (levi.val⁻¹ * first.val * levi.val)
      (levi.val⁻¹ * second * levi.val) = 0) :
    mixedValue Γ ρ c levi.val (first.val * second) =
      mixedValue Γ ρ c levi.val first.val +
        ρ first.val (mixedValue Γ ρ c levi.val second) := by
  have left := barValue_cocycle Γ ρ c levi
    (levi.val⁻¹ * first.val * levi.val) (levi.val⁻¹ * second * levi.val)
  have middle := barValue_cocycle Γ ρ c first levi.val
    (levi.val⁻¹ * second * levi.val)
  have right := barValue_cocycle Γ ρ c first second levi.val
  rw [conjugate_pure, map_zero] at left
  rw [pure] at right
  simp only [mul_assoc, mul_inv_cancel_left,
    sub_zero, zero_sub] at left middle right
  unfold mixedValue
  rw [map_sub]
  simp only [mul_assoc]
  have combined := congrArg₂ (fun firstValue secondValue : V => firstValue + secondValue)
    (congrArg₂ (fun firstValue secondValue : V => firstValue - secondValue) left middle)
    right
  simp only [sub_zero, add_zero] at combined
  apply sub_eq_zero.mp
  convert combined using 1; abel

theorem mixedValue_levi_cocycle (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (c : cocycles Γ ρ)
    (first radical : Γ) (second : G)
    (pure : barValue Γ ρ c first.val second = 0) :
    mixedValue Γ ρ c (first.val * second) radical.val =
      mixedValue Γ ρ c first.val radical.val +
        ρ first.val (mixedValue Γ ρ c second
          (first.val⁻¹ * radical.val * first.val)) := by
  have left := barValue_cocycle Γ ρ c first second
    (second⁻¹ * first.val⁻¹ * radical.val * first.val * second)
  have middle := barValue_cocycle Γ ρ c first
    (first.val⁻¹ * radical.val * first.val) second
  have right := barValue_cocycle Γ ρ c radical first.val second
  rw [pure] at left right
  simp only [mul_assoc, mul_inv_cancel_left,
    sub_zero, map_zero, zero_sub] at left middle right
  unfold mixedValue
  rw [map_sub]
  simp only [mul_inv_rev, mul_assoc]
  have combined := congrArg₂ (fun firstValue secondValue : V => firstValue - secondValue)
    (congrArg₂ (fun firstValue secondValue : V => secondValue - firstValue) left middle)
    right
  simp only [sub_zero] at combined
  apply sub_eq_zero.mp
  convert combined using 1; abel

theorem barValue_factorization (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (c : cocycles Γ ρ)
    (firstRadical firstLevi secondRadical secondLevi : Γ)
    (pureRadical : barValue Γ ρ c firstRadical.val
      (firstLevi.val * secondRadical.val * firstLevi.val⁻¹) = 0)
    (pureLevi : barValue Γ ρ c firstLevi.val secondLevi.val = 0) :
    barValue Γ ρ c (firstRadical.val * firstLevi.val)
        (secondRadical.val * secondLevi.val) +
      barValue Γ ρ c firstRadical.val firstLevi.val +
      ρ (firstRadical.val * firstLevi.val)
        (barValue Γ ρ c secondRadical.val secondLevi.val) -
      barValue Γ ρ c
        (firstRadical.val * (firstLevi.val * secondRadical.val * firstLevi.val⁻¹))
        (firstLevi.val * secondLevi.val) =
      ρ firstRadical.val (mixedValue Γ ρ c firstLevi.val
        (firstLevi.val * secondRadical.val * firstLevi.val⁻¹)) := by
  let conjugate : Γ := firstLevi * secondRadical * firstLevi⁻¹
  have first := barValue_cocycle Γ ρ c firstRadical firstLevi.val
    (secondRadical.val * secondLevi.val)
  have second := barValue_cocycle Γ ρ c firstLevi secondRadical.val secondLevi.val
  have third := barValue_cocycle Γ ρ c conjugate firstLevi.val secondLevi.val
  have fourth := barValue_cocycle Γ ρ c firstRadical conjugate.val
    (firstLevi.val * secondLevi.val)
  have conjugate_eq : conjugate.val =
      firstLevi.val * secondRadical.val * firstLevi.val⁻¹ := rfl
  rw [pureLevi, map_zero] at third
  rw [conjugate_eq, pureRadical] at fourth
  rw [conjugate_eq] at third
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at third fourth
  unfold mixedValue
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left, map_sub]
  rw [map_mul, Module.End.mul_apply]
  have transformedSecond := congrArg (ρ firstRadical.val) second
  have transformedThird := congrArg (ρ firstRadical.val) third
  simp only [map_sub, map_add, map_zero] at transformedSecond transformedThird
  have combined := congrArg₂ (fun firstValue secondValue : V => firstValue + secondValue)
    (congrArg₂ (fun firstValue secondValue : V => firstValue - secondValue)
      (congrArg₂ (fun firstValue secondValue : V => secondValue - firstValue)
        first transformedSecond) transformedThird) fourth
  simp only [sub_zero, add_zero] at combined
  apply sub_eq_zero.mp
  convert combined using 1; abel

end MixedCocycles

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
