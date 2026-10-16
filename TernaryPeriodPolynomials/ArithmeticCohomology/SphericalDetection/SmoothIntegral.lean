module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Operations
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
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.ParametricIntegral
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
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


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem contDiffOn_integral_compact_support
    {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {measure : Measure X} [IsLocallyFiniteMeasure measure] {order : ℕ∞}
    {values : P → X → E} {domain : Set P} {support : Set X}
    (domain_open : IsOpen domain) (support_compact : IsCompact support)
    (vanishes : ∀ parameter argument, parameter ∈ domain → argument ∉ support →
      values parameter argument = 0)
    (smooth : ContDiffOn ℝ order (Function.uncurry values) (domain ×ˢ Set.univ)) :
    ContDiffOn ℝ order (fun parameter => ∫ argument, values parameter argument ∂measure) domain := by
  let pairing : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have reflection : ContDiff ℝ order (fun point : P × X => (point.1, -point.2)) :=
    contDiff_fst.prodMk contDiff_snd.neg
  have reflected_smooth : ContDiffOn ℝ order
      (fun point : P × X => values point.1 (-point.2)) (domain ×ˢ Set.univ) :=
    smooth.comp reflection.contDiffOn
      (fun _ member => ⟨member.1, Set.mem_univ _⟩)
  have reflected_support : ∀ parameter argument, parameter ∈ domain → argument ∉ -support →
      values parameter (-argument) = 0 := by
    intro parameter argument parameter_mem argument_out
    apply vanishes parameter (-argument) parameter_mem
    simpa only [Set.mem_neg] using argument_out
  have convolution_smooth := MeasureTheory.contDiffOn_convolution_right_with_param_aux
    (𝕜 := ℝ) (n := order) (f := fun _ : X => (1 : ℝ)) (μ := measure)
    pairing domain_open support_compact.neg reflected_support
    (continuous_const.locallyIntegrable) reflected_smooth
  have composed := convolution_smooth.comp
    (contDiff_id.prodMk (contDiff_const (c := (0 : X)))).contDiffOn
    (fun _ member => ⟨member, Set.mem_univ _⟩)
  simpa only [MeasureTheory.convolution, Function.uncurry_def, Function.comp_def, id_eq, zero_sub, neg_neg,
    pairing, ContinuousLinearMap.lsmul_apply, one_smul] using composed

end TernaryPeriodPolynomials.SphericalDetection.Helpers
