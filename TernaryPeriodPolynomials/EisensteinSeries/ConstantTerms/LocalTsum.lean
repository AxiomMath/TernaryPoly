module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.Basic
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
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Set.Pointwise.Support
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
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Termwise differentiation of series on an open set (cutoff argument)

A series of `C^∞` functions on an open set `U ⊂ ℝ⁵` with summable bounds on the iterated derivatives
over every compact subset of `U` is `C^∞` on `U` and its iterated derivatives are the sums of the
iterated derivatives. (Mathlib's `contDiff_tsum` is global; we localize with a bump function.)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff

/-! ### Local termwise differentiation of series on an open set -/

theorem contDiff_cutoff_smul {U : Set (Fin 5 → ℝ)} (hU : IsOpen U) {c : Fin 5 → ℝ}
    (χ : ContDiffBump c) (hχU : Metric.closedBall c χ.rOut ⊆ U) {t : (Fin 5 → ℝ) → ℂ}
    (ht : ContDiffOn ℝ ∞ t U) : ContDiff ℝ ∞ (fun x => χ x • t x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (χ.contDiff.contDiffAt).smul ((ht.contDiffAt (hU.mem_nhds hx)))
  · have hxs : x ∉ tsupport (χ : (Fin 5 → ℝ) → ℝ) := by
      rw [χ.tsupport_eq]; exact fun h => hx (hχU h)
    have hz : (fun y => χ y • t y) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      have := (notMem_tsupport_iff_eventuallyEq.1 hxs)
      filter_upwards [this] with y hy
      simp [hy]
    exact (contDiffAt_const).congr_of_eventuallyEq hz

theorem iteratedFDeriv_cutoff_eq_zero {c : Fin 5 → ℝ}
    (χ : ContDiffBump c) (t : (Fin 5 → ℝ) → ℂ) (k : ℕ) {x : Fin 5 → ℝ}
    (hx : x ∉ Metric.closedBall c χ.rOut) :
    iteratedFDeriv ℝ k (fun y => χ y • t y) x = 0 := by
  have hxs : x ∉ tsupport (χ : (Fin 5 → ℝ) → ℝ) := by
    rw [χ.tsupport_eq]; exact hx
  have hz : (fun y => χ y • t y) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    have := (notMem_tsupport_iff_eventuallyEq.1 hxs)
    filter_upwards [this] with y hy
    simp [hy]
  rw [(hz.iteratedFDeriv ℝ k).eq_of_nhds]
  cases k with
  | zero => ext; simp
  | succ k => simp

theorem contDiffOn_tsum_local {α : Type*} {U : Set (Fin 5 → ℝ)} (hU : IsOpen U)
    (f : α → (Fin 5 → ℝ) → ℂ) (hf : ∀ c, ContDiffOn ℝ ∞ (f c) U)
    (hb : ∀ K : Set (Fin 5 → ℝ), IsCompact K → K ⊆ U → ∀ k : ℕ, ∃ b : α → ℝ, Summable b ∧
      ∀ c, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (f c) x‖ ≤ b c) :
    ContDiffOn ℝ ∞ (fun x => ∑' c, f c x) U ∧
      ∀ (k : ℕ), ∀ x ∈ U, iteratedFDeriv ℝ k (fun y => ∑' c, f c y) x =
        ∑' c, iteratedFDeriv ℝ k (f c) x := by
  have hloc : ∀ q₀ ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball q₀ r ⊆ U ∧
      ContDiffOn ℝ ∞ (fun x => ∑' c, f c x) (Metric.ball q₀ r) ∧
      ∀ (k : ℕ), ∀ x ∈ Metric.ball q₀ r, iteratedFDeriv ℝ k (fun y => ∑' c, f c y) x =
        ∑' c, iteratedFDeriv ℝ k (f c) x := by
    intro q₀ hq₀
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU q₀ hq₀
    set r : ℝ := ε / 4 with hr
    have hr0 : 0 < r := by positivity
    let χ : ContDiffBump q₀ := ⟨r, 2 * r, hr0, by linarith⟩
    have hKU : Metric.closedBall q₀ χ.rOut ⊆ U := by
      refine (Metric.closedBall_subset_ball ?_).trans hεU
      show 2 * r < ε
      rw [hr]; linarith
    have hKc : IsCompact (Metric.closedBall q₀ χ.rOut) := isCompact_closedBall _ _
    set g : α → (Fin 5 → ℝ) → ℂ := fun c x => χ x • f c x with hgdef
    have hg : ∀ c, ContDiff ℝ ∞ (g c) := fun c => contDiff_cutoff_smul hU χ hKU (hf c)
    have hχb : ∀ i : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (χ : (Fin 5 → ℝ) → ℝ) x‖ ≤ M := by
      intro i
      have hcs : HasCompactSupport (iteratedFDeriv ℝ i (χ : (Fin 5 → ℝ) → ℝ)) :=
        χ.hasCompactSupport.iteratedFDeriv i
      have hco : Continuous (iteratedFDeriv ℝ i (χ : (Fin 5 → ℝ) → ℝ)) :=
        χ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)
      obtain ⟨M, hM⟩ := hco.bounded_above_of_compact_support hcs
      exact ⟨M, hM⟩
    choose M hM using hχb
    choose b hbs hbb using fun j => hb _ hKc hKU j
    have hq₀K : q₀ ∈ Metric.closedBall q₀ χ.rOut :=
      Metric.mem_closedBall_self (by linarith [χ.rIn_pos, χ.rIn_lt_rOut])
    have hMi0 : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i q₀)
    have hv : ∀ k : ℕ, ∃ v : α → ℝ, Summable v ∧ ∀ c x, ‖iteratedFDeriv ℝ k (g c) x‖ ≤ v c := by
      intro k
      refine ⟨fun c => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M i * b (k - i) c,
        summable_sum fun i _ => ((hbs (k - i)).mul_left _), fun c x => ?_⟩
      by_cases hx : x ∈ Metric.closedBall q₀ χ.rOut
      · have hxU := hKU hx
        have hLeib := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (f := (χ : (Fin 5 → ℝ) → ℝ))
          (g := f c) (s := U) (N := ∞) χ.contDiff.contDiffOn (hf c) hU.uniqueDiffOn hxU
          (n := k) (by exact_mod_cast le_top)
        have h1 : ‖iteratedFDeriv ℝ k (g c) x‖ = ‖iteratedFDerivWithin ℝ k (g c) U x‖ := by
          rw [iteratedFDerivWithin_of_isOpen k hU hxU]
        rw [h1]
        refine hLeib.trans (Finset.sum_le_sum fun i hi => ?_)
        rw [iteratedFDerivWithin_of_isOpen i hU hxU, iteratedFDerivWithin_of_isOpen (k - i) hU hxU]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hM i x) (Nat.cast_nonneg _))
          (hbb (k - i) c x hx) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hMi0 i))
      · rw [iteratedFDeriv_cutoff_eq_zero χ (f c) k hx]
        simp only [norm_zero]
        refine Finset.sum_nonneg fun i _ => ?_
        have : 0 ≤ b (k - i) c := (norm_nonneg _).trans (hbb (k - i) c q₀ hq₀K)
        have := hMi0 i
        positivity
    choose v hvs hvb using hv
    have hGsm : ContDiff ℝ ∞ (fun x => ∑' c, g c x) :=
      contDiff_tsum hg (fun k _ => hvs k) (fun k c x _ => hvb k c x)
    have hGit : ∀ k : ℕ, (iteratedFDeriv ℝ k fun y => ∑' c, g c y) =
        fun x => ∑' c, iteratedFDeriv ℝ k (g c) x := fun k =>
      iteratedFDeriv_tsum hg (fun k _ => hvs k) (fun k c x _ => hvb k c x) (k := k)
        (by exact_mod_cast le_top)
    -- on the small ball the cutoff is 1
    have hball : Metric.ball q₀ r ⊆ Metric.closedBall q₀ χ.rIn := Metric.ball_subset_closedBall
    have hev : ∀ x ∈ Metric.ball q₀ r, (fun y => ∑' c, f c y) =ᶠ[nhds x] fun y => ∑' c, g c y := by
      intro x hx
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      have : χ y = 1 := χ.one_of_mem_closedBall (hball hy)
      simp [hgdef, this]
    have hevc : ∀ c, ∀ x ∈ Metric.ball q₀ r, g c =ᶠ[nhds x] f c := by
      intro c x hx
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      have : χ y = 1 := χ.one_of_mem_closedBall (hball hy)
      simp [hgdef, this]
    refine ⟨r, hr0, ?_, ?_, ?_⟩
    · intro x hx
      exact hεU (Metric.ball_subset_ball (by rw [hr]; linarith) hx)
    · intro x hx
      exact (hGsm.contDiffAt.congr_of_eventuallyEq (hev x hx)).contDiffWithinAt
    · intro k x hx
      rw [(((hev x hx).iteratedFDeriv ℝ k).eq_of_nhds), hGit k]
      exact tsum_congr fun c => ((hevc c x hx).iteratedFDeriv ℝ k).eq_of_nhds
  refine ⟨?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    obtain ⟨r, hr, hrU, hsm, -⟩ := hloc x hx
    exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      hsm.mono Set.inter_subset_right⟩
  · intro k x hx
    obtain ⟨r, hr, hrU, -, hit⟩ := hloc x hx
    exact hit k x (Metric.mem_ball_self hr)

end TernaryPeriodPolynomials.Argument.ConvergenceC4
