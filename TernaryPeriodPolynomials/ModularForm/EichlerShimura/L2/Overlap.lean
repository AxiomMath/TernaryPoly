module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Data.List.Enum
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Interchanging a sum with an inner product integral

If a function `x` is, pointwise almost everywhere, a sum of functions `A i` with uniformly bounded
overlap and summable squared `L²` norms, then the integral of `⟪x, u⟫` against an `L²` function `u`
is the sum of the integrals of `⟪A i, u⟫`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ENNReal

theorem integral_tsum_inner {α ι X : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {A : ι → α → X} {u x : α → X} (hA : ∀ i, AEStronglyMeasurable (A i) μ)
    (hu : AEStronglyMeasurable u μ)
    (hsum : ∑' i, ∫⁻ a, ENNReal.ofReal (‖A i a‖ ^ 2) ∂μ < ⊤)
    (hu2 : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2) ∂μ < ⊤)
    {N : ℕ} (hN : ∀ᵐ a ∂μ, {i | A i a ≠ 0}.Finite ∧ {i | A i a ≠ 0}.ncard ≤ N)
    (hx : ∀ᵐ a ∂μ, x a = ∑ᶠ i, A i a) :
    (∀ i, Integrable (fun a => ⟪A i a, u a⟫_ℝ) μ) ∧
      Summable (fun i => ∫ a, ‖⟪A i a, u a⟫_ℝ‖ ∂μ) ∧
      HasSum (fun i => ∫ a, ⟪A i a, u a⟫_ℝ ∂μ) (∫ a, ⟪x a, u a⟫_ℝ ∂μ) := by
  set F : ι → α → ℝ := fun i a => ⟪A i a, u a⟫_ℝ with hF
  have hFm : ∀ i, AEStronglyMeasurable (F i) μ := fun i => (hA i).inner hu
  -- pointwise bound
  have hpt : ∀ᵐ a ∂μ, ∑' i, ‖F i a‖ₑ ≤
      ∑' i, ENNReal.ofReal (‖A i a‖ ^ 2) + N * ENNReal.ofReal (‖u a‖ ^ 2) := by
    filter_upwards [hN] with a hNa
    obtain ⟨hfin, hcard⟩ := hNa
    set J := hfin.toFinset with hJ
    have hzero : ∀ i ∉ J, ‖F i a‖ₑ = 0 := by
      intro i hi
      have : A i a = 0 := by
        by_contra h
        exact hi (hfin.mem_toFinset.mpr h)
      simp [hF, this]
    rw [tsum_eq_sum hzero]
    have hb : ∀ i ∈ J, ‖F i a‖ₑ ≤ ENNReal.ofReal (‖A i a‖ ^ 2) + ENNReal.ofReal (‖u a‖ ^ 2) := by
      intro i _
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : |⟪A i a, u a⟫_ℝ| ≤ ‖A i a‖ * ‖u a‖ := abs_real_inner_le_norm _ _
      nlinarith [sq_nonneg (‖A i a‖ - ‖u a‖), norm_nonneg (A i a), norm_nonneg (u a)]
    calc ∑ i ∈ J, ‖F i a‖ₑ ≤ ∑ i ∈ J, (ENNReal.ofReal (‖A i a‖ ^ 2) + ENNReal.ofReal (‖u a‖ ^ 2)) :=
          Finset.sum_le_sum hb
      _ = ∑ i ∈ J, ENNReal.ofReal (‖A i a‖ ^ 2) + J.card * ENNReal.ofReal (‖u a‖ ^ 2) := by
          rw [Finset.sum_add_distrib]
          simp
      _ ≤ _ := by
          refine add_le_add (ENNReal.sum_le_tsum _) ?_
          gcongr
          have : J.card = {i | A i a ≠ 0}.ncard := by
            rw [hJ, Set.ncard_eq_toFinset_card _ hfin]
          rw [this]
          exact_mod_cast hcard
  have hAm : ∀ i, AEMeasurable (fun a => ENNReal.ofReal (‖A i a‖ ^ 2)) μ := fun i =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((hA i).norm.aemeasurable.pow_const 2)
  have hum : AEMeasurable (fun a => ENNReal.ofReal (‖u a‖ ^ 2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hu.norm.aemeasurable.pow_const 2)
  have hint : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae hpt) ?_
    rw [lintegral_add_right' _ (hum.const_mul _), lintegral_tsum hAm,
      lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
    exact ENNReal.add_lt_top.mpr ⟨hsum, ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) hu2⟩
  have hFe : ∀ i, AEMeasurable (fun a => ‖F i a‖ₑ) μ := fun i => (hFm i).enorm
  have hsum' : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ < ⊤ := by
    rw [← lintegral_tsum hFe]; exact hint
  have hFi : ∀ i, Integrable (F i) μ := fun i =>
    ⟨hFm i, (ENNReal.le_tsum i).trans_lt hsum'⟩
  have hFs : Summable fun i => ∫ a, ‖F i a‖ ∂μ := by
    have : ∀ i, ∫ a, ‖F i a‖ ∂μ = (∫⁻ a, ‖F i a‖ₑ ∂μ).toReal := fun i =>
      integral_norm_eq_lintegral_enorm (hFm i)
    simp_rw [this]
    exact ENNReal.summable_toReal hsum'.ne
  refine ⟨hFi, hFs, ?_⟩
  have h := hasSum_integral_of_summable_integral_norm hFi hFs
  have e : ∫ a, ⟪x a, u a⟫_ℝ ∂μ = ∫ a, ∑' i, F i a ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hx, hN] with a ha hNa
    obtain ⟨hfin, -⟩ := hNa
    have hsupp : Function.support (fun i => A i a) ⊆ (hfin.toFinset : Set ι) := by
      intro i hi
      simpa using hi
    rw [ha, finsum_eq_sum_of_support_subset _ hsupp, sum_inner]
    rw [tsum_eq_sum (s := hfin.toFinset)]
    intro i hi
    have : A i a = 0 := by
      by_contra h
      exact hi (hfin.mem_toFinset.mpr h)
    simp [hF, this]
  rw [e]
  exact h

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
