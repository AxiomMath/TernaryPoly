module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.StandardBorel
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem rational_pair_reduction (x y : ℚ) :
    ∃ a b c d : ℤ, a*d-b*c = 1 ∧ (c : ℚ)*x+(d : ℚ)*y = 0 := by
  by_cases zero : y = 0
  · exact ⟨1,0,0,1,by norm_num,by simp [zero]⟩
  · let q := x/y
    obtain ⟨a,b,bezout⟩ := q.isCoprime_num_den
    refine ⟨a,b,-(q.den : ℤ),q.num,?_,?_⟩
    · convert bezout using 1
      ring
    · have denominator : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      have ratio := q.num_div_den
      change (q.num : ℚ)/(q.den : ℚ) = x/y at ratio
      have cross := (div_eq_div_iff denominator zero).mp ratio
      simp only [Int.cast_neg,Int.cast_natCast,neg_mul]
      linear_combination cross

def integralPair01 (a b c d : ℤ) (determinant : a*d-b*c = 1) : IntegralGL3 :=
  ⟨!![a,b,0;c,d,0;0,0,1],!![d,-b,0;-c,a,0;0,0,1],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three] <;> nlinarith [determinant],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three] <;> nlinarith [determinant]⟩

def integralPair12 (a b c d : ℤ) (determinant : a*d-b*c = 1) : IntegralGL3 :=
  ⟨!![1,0,0;0,a,b;0,c,d],!![1,0,0;0,d,-b;0,-c,a],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three] <;> nlinarith [determinant],by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three] <;> nlinarith [determinant]⟩

theorem integralPair01_rows (a b c d : ℤ) (determinant : a*d-b*c = 1)
    (g : RationalGL3) (j : Fin 3) :
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralPair01 a b c d determinant)*g).val 1 j =
      (c : ℚ)*g.val 0 j+(d : ℚ)*g.val 1 j ∧
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralPair01 a b c d determinant)*g).val 2 j =
      g.val 2 j := by
  simp [integralPair01,Matrix.mul_apply,Fin.sum_univ_three]

theorem integralPair12_rows (a b c d : ℤ) (determinant : a*d-b*c = 1)
    (g : RationalGL3) (j : Fin 3) :
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralPair12 a b c d determinant)*g).val 1 j =
      (a : ℚ)*g.val 1 j+(b : ℚ)*g.val 2 j ∧
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralPair12 a b c d determinant)*g).val 2 j =
      (c : ℚ)*g.val 1 j+(d : ℚ)*g.val 2 j := by
  simp [integralPair12,Matrix.mul_apply,Fin.sum_univ_three]

theorem rational_flag_integral_representative (g : RationalGL3) :
    ∃ V : IntegralGL3,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) V) : Edges) = QuotientGroup.mk g := by
  let cast : IntegralGL3 →* RationalGL3 := GeneralLinearGroup.map (Int.castRingHom ℚ)
  obtain ⟨a,b,c,d,det₁,zero₁⟩ := rational_pair_reduction (g.val 1 0) (g.val 2 0)
  let P := integralPair12 a b c d det₁
  let g₁ := cast P*g
  have bottom_zero : g₁.val 2 0 = 0 := by
    rw [(integralPair12_rows a b c d det₁ g 0).2]
    exact zero₁
  obtain ⟨a',b',c',d',det₂,zero₂⟩ := rational_pair_reduction (g₁.val 0 0) (g₁.val 1 0)
  let Q := integralPair01 a' b' c' d' det₂
  let g₂ := cast Q*g₁
  have middle_zero : g₂.val 1 0 = 0 := by
    rw [(integralPair01_rows a' b' c' d' det₂ g₁ 0).1]
    exact zero₂
  have bottom_zero₂ : g₂.val 2 0 = 0 := by
    rw [(integralPair01_rows a' b' c' d' det₂ g₁ 0).2]
    exact bottom_zero
  obtain ⟨a'',b'',c'',d'',det₃,zero₃⟩ := rational_pair_reduction (g₂.val 1 1) (g₂.val 2 1)
  let R := integralPair12 a'' b'' c'' d'' det₃
  let g₃ := cast R*g₂
  have bottom_one : g₃.val 2 1 = 0 := by
    rw [(integralPair12_rows a'' b'' c'' d'' det₃ g₂ 1).2]
    exact zero₃
  have middle_zero₃ : g₃.val 1 0 = 0 := by
    rw [(integralPair12_rows a'' b'' c'' d'' det₃ g₂ 0).1,middle_zero,bottom_zero₂]
    ring
  have bottom_zero₃ : g₃.val 2 0 = 0 := by
    rw [(integralPair12_rows a'' b'' c'' d'' det₃ g₂ 0).2,middle_zero,bottom_zero₂]
    ring
  refine ⟨(R*(Q*P))⁻¹,?_⟩
  apply QuotientGroup.eq.mpr
  rw [map_inv,inv_inv,map_mul,map_mul]
  change (cast R*(cast Q*cast P))*g ∈ parabolic .plane ⊓ parabolic .line
  rw [mul_assoc,mul_assoc]
  exact ⟨⟨bottom_zero₃,bottom_one⟩,⟨middle_zero₃,bottom_zero₃⟩⟩

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
