module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Extracting a Fourier coefficient of an absolutely convergent trigonometric series

If `Σ_n (e^{i(k+2n)θ} P_n + e^{-i(k+2n)θ} Q_n)` converges absolutely and vanishes for every real
`θ` (with `k > 0`), then `Q_0 = 0`: multiply by `e^{ikθ}` and integrate over `[0, 2π]`; the only
frequency that survives is the one of `Q_0`.
-/

noncomputable section

open MeasureTheory Complex intervalIntegral

namespace TernaryPeriodPolynomials.Regularity

/-- `∫₀^{2π} e^{i m θ} dθ = 0` for a nonzero integer `m`. -/
theorem integral_exp_int_mul_I {m : ℤ} (hm : m ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), cexp ((m : ℂ) * I * θ) = 0 := by
  have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hm) I_ne_zero
  rw [integral_exp_mul_complex hc]
  have h2 : cexp ((m : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show (m : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ) = m * (2 * Real.pi * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [h2]
  simp

/-- `∫₀^{2π} e^{-i m θ} dθ = 0` for a nonzero integer `m`. -/
theorem integral_exp_neg_int_mul_I {m : ℤ} (hm : m ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), cexp (-(m : ℂ) * I * θ) = 0 := by
  have h := integral_exp_int_mul_I (neg_ne_zero.mpr hm)
  simpa only [Int.cast_neg] using h

/-- If an absolutely convergent series `Σ (e^{i(k+2n)θ} P n + e^{-i(k+2n)θ} Q n)` vanishes for
every `θ` and `k > 0`, then `Q 0 = 0`. -/
theorem coeff_zero_of_tsum_eq_zero {k : ℕ} (hk : 0 < k) {P Q : ℕ → ℂ}
    (hP : Summable fun n => ‖P n‖) (hQ : Summable fun n => ‖Q n‖)
    (h : ∀ θ : ℝ, ∑' n : ℕ, (cexp ((((k : ℂ) + 2 * n) * θ) * I) * P n +
      cexp (-(((k : ℂ) + 2 * n) * θ) * I) * Q n) = 0) : Q 0 = 0 := by
  let f : ℕ → ℝ → ℂ := fun n θ => cexp ((k : ℂ) * θ * I) *
    (cexp ((((k : ℂ) + 2 * n) * θ) * I) * P n + cexp (-(((k : ℂ) + 2 * n) * θ) * I) * Q n)
  have hexp : ∀ (n : ℕ) (θ : ℝ), f n θ =
      cexp ((((2 * k + 2 * n : ℕ) : ℤ) : ℂ) * I * θ) * P n +
        cexp (-((((2 * n : ℕ) : ℤ)) : ℂ) * I * θ) * Q n := by
    intro n θ
    simp only [f]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 3 <;> push_cast <;> ring
  have hcont : ∀ n, Continuous (f n) := fun n => by
    have : f n = fun θ : ℝ => cexp ((((2 * k + 2 * n : ℕ) : ℤ) : ℂ) * I * θ) * P n +
        cexp (-((((2 * n : ℕ) : ℤ)) : ℂ) * I * θ) * Q n := funext (hexp n)
    rw [this]
    fun_prop
  have hnorm1 : ∀ z : ℂ, z.re = 0 → ‖cexp z‖ = 1 := by
    intro z hz
    rw [Complex.norm_exp, hz, Real.exp_zero]
  have hnorm : ∀ n θ, ‖f n θ‖ ≤ ‖P n‖ + ‖Q n‖ := by
    intro n θ
    rw [hexp n θ]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact le_of_eq (by rw [norm_mul, hnorm1 _ (by simp), one_mul])
    · exact le_of_eq (by rw [norm_mul, hnorm1 _ (by simp), one_mul])
  have hterm : ∀ n : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), f n θ =
      if n = 0 then (2 * Real.pi : ℂ) * Q 0 else 0 := by
    intro n
    have hfun : f n = fun θ : ℝ => cexp ((((2 * k + 2 * n : ℕ) : ℤ) : ℂ) * I * θ) * P n +
        cexp (-((((2 * n : ℕ) : ℤ)) : ℂ) * I * θ) * Q n := funext (hexp n)
    rw [hfun, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const,
      integral_exp_int_mul_I (m := ((2 * k + 2 * n : ℕ) : ℤ))
        (by exact_mod_cast (show 2 * k + 2 * n ≠ 0 by omega)), zero_mul,
      zero_add]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [integral_exp_neg_int_mul_I (m := ((2 * n : ℕ) : ℤ))
        (by exact_mod_cast (show 2 * n ≠ 0 by omega)), zero_mul, ite_eq_right hn]
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hsum : ∑' n, ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ‖f n θ‖ₑ ≠ ⊤ := by
    have hb : ∀ n, ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ‖f n θ‖ₑ ≤
        ENNReal.ofReal (‖P n‖ + ‖Q n‖) * ENNReal.ofReal (2 * Real.pi) := by
      intro n
      calc ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ‖f n θ‖ₑ
          ≤ ∫⁻ _ in Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (‖P n‖ + ‖Q n‖) :=
            lintegral_mono fun θ => by
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hnorm n θ)
        _ = ENNReal.ofReal (‖P n‖ + ‖Q n‖) * ENNReal.ofReal (2 * Real.pi) := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
      (fun n => add_nonneg (norm_nonneg _) (norm_nonneg _)) (hP.add hQ)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hswap := integral_tsum (μ := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
    (fun n => (hcont n).aestronglyMeasurable) hsum
  have hzero : ∀ θ, ∑' n, f n θ = 0 := fun θ => by
    simp only [f]
    rw [tsum_mul_left, h θ, mul_zero]
  simp only [hzero, MeasureTheory.integral_zero] at hswap
  have hval : ∑' n, ∫ θ in Set.Ioc 0 (2 * Real.pi), f n θ = (2 * Real.pi : ℂ) * Q 0 := by
    have : ∀ n, ∫ θ in Set.Ioc 0 (2 * Real.pi), f n θ =
        if n = 0 then (2 * Real.pi : ℂ) * Q 0 else 0 := fun n => by
      rw [← intervalIntegral.integral_of_le hle, hterm n]
    rw [tsum_congr this, tsum_ite_eq]
  rw [hval] at hswap
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  exact (mul_eq_zero.mp hswap.symm).resolve_left hπ

end TernaryPeriodPolynomials.Regularity

end
