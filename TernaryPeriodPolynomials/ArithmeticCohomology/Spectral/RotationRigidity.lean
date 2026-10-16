module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
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
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Real.Cardinality
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
# Rigidity of functions with a rotation-type functional equation

If `h` is holomorphic on the unit disc and `h (κ w) = c · h w` there, with `κ^N ≠ c` for
every `N`, then `h` vanishes on the disc: comparing the leading terms `w^N u(w)` at the origin forces
`κ^N = c`. This is the analytic half of the elliptic-element argument in `LevelOneMultiplicityOne`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Filter Topology Metric

namespace TernaryPeriodPolynomials.Spectral.RotationRigidity

theorem eq_zero_of_rotation {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1)) {κ c : ℂ}
    (hc : ∀ N : ℕ, κ ^ N ≠ c)
    (heq : ∀ w ∈ ball (0 : ℂ) 1, h (κ * w) = c * h w) : ∀ w ∈ ball (0 : ℂ) 1, h w = 0 := by
  have hopen : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have hanalytic : AnalyticOnNhd ℂ h (ball 0 1) := fun z hz =>
    hh.analyticAt (hopen.mem_nhds hz)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hzero : ∀ᶠ w in 𝓝 (0 : ℂ), h w = 0 := by
    by_contra hnot
    obtain ⟨n, u, hu, hu0, hfac⟩ :=
      ((hanalytic 0 h0).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
    -- `κ w` tends to `0` with `w`
    have htend : Tendsto (fun w : ℂ => κ * w) (𝓝 0) (𝓝 0) := by
      have := (continuous_const_mul κ).tendsto 0
      rwa [mul_zero] at this
    have hfac' : ∀ᶠ w in 𝓝 (0 : ℂ), h (κ * w) = (κ * w - 0) ^ n • u (κ * w) :=
      htend.eventually hfac
    have hball : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ball (0 : ℂ) 1 := hopen.mem_nhds h0
    -- on a punctured neighbourhood, `κ^n u(κ w) = c u(w)`
    have hpunct : ∀ᶠ w in 𝓝[≠] (0 : ℂ), κ ^ n * u (κ * w) - c * u w = 0 := by
      have h1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ≠ 0 := self_mem_nhdsWithin
      filter_upwards [nhdsWithin_le_nhds hfac, nhdsWithin_le_nhds hfac',
        nhdsWithin_le_nhds hball, h1] with w hw hw' hwb hw0
      have hrel := heq w hwb
      rw [hw', hw] at hrel
      simp only [sub_zero, smul_eq_mul, mul_pow] at hrel
      have hwn : w ^ n ≠ 0 := pow_ne_zero n hw0
      have : w ^ n * (κ ^ n * u (κ * w) - c * u w) = 0 := by linear_combination hrel
      exact (mul_eq_zero.mp this).resolve_left hwn
    have hcont : ContinuousAt (fun w : ℂ => κ ^ n * u (κ * w) - c * u w) 0 := by
      have hu' : ContinuousAt u 0 := hu.continuousAt
      have hcomp : ContinuousAt (fun w : ℂ => u (κ * w)) 0 := by
        have : ContinuousAt u (κ * 0) := by simpa using hu'
        exact this.comp (continuous_const.mul continuous_id).continuousAt
      exact (continuousAt_const.mul hcomp).sub (continuousAt_const.mul hu')
    have hlim : Tendsto (fun w : ℂ => κ ^ n * u (κ * w) - c * u w) (𝓝[≠] 0)
        (𝓝 (κ ^ n * u (κ * 0) - c * u 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hlim0 : Tendsto (fun w : ℂ => κ ^ n * u (κ * w) - c * u w) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hpunct.mono fun w hw => hw.symm)
    have hval := tendsto_nhds_unique hlim hlim0
    rw [mul_zero] at hval
    have : (κ ^ n - c) * u 0 = 0 := by linear_combination hval
    rcases mul_eq_zero.mp this with h' | h'
    · exact hc n (sub_eq_zero.mp h')
    · exact hu0 h'
  have := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected h0 hzero
  intro w hw
  exact this hw

end TernaryPeriodPolynomials.Spectral.RotationRigidity
