module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.AngularSum
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

@[expose] public section


/-! Integrates `angularIntegrand n r θ` over `θ ∈ [0, 2π]` termwise against the double-sum
expansion from `AngularSum.lean`: each `exp(i·2(j+l)·θ)` term integrates to `2π` if `j+l=0`
and to `0` otherwise, and the double sum collapses to its single `j=l=0` term. This proves
Clause 1 of `real_constant_term_entry` (Appendix C.5, `ar:eq:cinfty`). -/


namespace TernaryPeriodPolynomials.Argument

theorem angular_term_integral (p : ℕ) :
    ∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (Complex.I * (2*(p:ℂ)) * θ) =
      if p = 0 then (2*Real.pi : ℂ) else 0 := by
  by_cases hp : p = 0
  · subst hp; simp
  · rw [ite_eq_right hp]
    have hp' : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
    have hc : Complex.I * (2*(p:ℂ)) ≠ 0 := by
      apply mul_ne_zero Complex.I_ne_zero
      apply mul_ne_zero two_ne_zero
      exact_mod_cast hp'
    rw [integral_exp_mul_complex hc]
    have e1 : Complex.I * (2*(p:ℂ)) * ((2*Real.pi:ℝ):ℂ) =
        (2*p:ℕ) * (2*(Real.pi:ℂ)*Complex.I) := by push_cast; ring
    have e2 : Complex.I * (2*(p:ℂ)) * ((0:ℝ):ℂ) = 0 := by push_cast; ring
    rw [e1, e2, Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_zero]
    ring

theorem angular_term_integral' (j l : ℕ) :
    ∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (Complex.I*(2*((j:ℂ)+(l:ℂ)))*θ) =
      if j + l = 0 then (2*Real.pi : ℂ) else 0 := by
  have h := angular_term_integral (j+l)
  rw [show ((j+l:ℕ):ℂ) = (j:ℂ)+(l:ℂ) by push_cast; ring] at h
  exact h

/-- A double sum over `j ∈ range 4`, `l ∈ range (n+1)` of a term that vanishes unless
`j + l = 0` collapses to its `j = l = 0` term. -/
theorem double_sum_collapse (A B : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range 4, ∑ l ∈ Finset.range (n+1),
      A j * B l * (if j + l = 0 then (2*Real.pi:ℂ) else 0) =
      A 0 * B 0 * (2*Real.pi) := by
  have hl : ∀ j : ℕ, 0 < j → ∑ l ∈ Finset.range (n+1),
      A j * B l * (if j + l = 0 then (2*Real.pi:ℂ) else 0) = 0 := by
    intro j hj
    apply Finset.sum_eq_zero
    intro l _
    rw [ite_eq_right (by omega), mul_zero]
  have h0 : ∑ l ∈ Finset.range (n+1),
      A 0 * B l * (if 0 + l = 0 then (2*Real.pi:ℂ) else 0) = A 0 * B 0 * (2*Real.pi) := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) (by
      intro l _ hl
      rw [ite_eq_right (by omega), mul_zero])]
    norm_num
  rw [Finset.sum_eq_single_of_mem (0:ℕ) (Finset.mem_range.mpr (by omega))
    (fun j _ hj0 => hl j (Nat.pos_of_ne_zero hj0))]
  exact h0

/-- **Clause 1 of `real_constant_term_entry`.** -/
theorem real_constant_term_entry_clause1 (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∫ θ in (0:ℝ)..(2*Real.pi), angularIntegrand n r θ =
      2*Real.pi * ((r:ℂ)+1)^(n+3) / (2^(n+3) * (r:ℂ)^n) := by
  have hswap1 : (∫ θ in (0:ℝ)..(2*Real.pi),
      ∑ j ∈ Finset.range 4, ∑ l ∈ Finset.range (n+1),
        (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
        ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
        Complex.exp (Complex.I*(2*((j:ℂ)+l))*θ)) =
      ∑ j ∈ Finset.range 4, ∑ l ∈ Finset.range (n+1),
        ∫ θ in (0:ℝ)..(2*Real.pi),
          (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
          ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
          Complex.exp (Complex.I*(2*((j:ℂ)+l))*θ) := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_finsetSum]
      intro l _
      apply Continuous.intervalIntegrable
      fun_prop
    · intro j _
      apply Continuous.intervalIntegrable
      fun_prop
  have hstep1 : (∫ θ in (0:ℝ)..(2*Real.pi), angularIntegrand n r θ) =
      ∫ θ in (0:ℝ)..(2*Real.pi),
        (∑ j ∈ Finset.range 4, ∑ l ∈ Finset.range (n+1),
          (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
          ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
          Complex.exp (Complex.I*(2*((j:ℂ)+l))*θ)) / (2^3 * 2^n) := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact angularIntegrand_eq_doublesum2 n r θ
  rw [hstep1, intervalIntegral.integral_div, hswap1]
  have hterm : ∀ j ∈ Finset.range 4, ∀ l ∈ Finset.range (n+1),
      (∫ θ in (0:ℝ)..(2*Real.pi),
        (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
        ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
        Complex.exp (Complex.I*(2*((j:ℂ)+l))*θ)) =
      (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
      ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
      (if j + l = 0 then (2*Real.pi:ℂ) else 0) := by
    intro j _ l _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact angular_term_integral' j l
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun l hl => hterm j hj l hl))]
  have hcol := double_sum_collapse
    (fun j => (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)))
    (fun l => ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l))) n
  rw [hcol]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero, mul_one]
  have hr1 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpow : (1 + ((1/r:ℝ):ℂ))^n = ((r:ℂ)+1)^n / (r:ℂ)^n := by
    rw [show ((1/r:ℝ):ℂ) = 1/(r:ℂ) from by push_cast; ring,
        show (1:ℂ) + 1/(r:ℂ) = ((r:ℂ)+1)/(r:ℂ) from by field_simp, div_pow]
  rw [hpow]
  field_simp
  ring

end TernaryPeriodPolynomials.Argument
