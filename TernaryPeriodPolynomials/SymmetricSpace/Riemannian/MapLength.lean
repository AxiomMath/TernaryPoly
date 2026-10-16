module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
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
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Actual path lengths and intrinsic distances under tangent-norm-preserving smooth maps. -/
namespace TernaryPoly.RiemannianMapLength

open Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : M', ENorm (TangentSpace I' x)]

/-- Literal integral equality follows from the chain rule and preservation of tangent norms. -/
theorem pathELength_comp (f : M → M') (hf : MDifferentiable I I' f)
    (hnorm : ∀ x v, ‖mfderiv I I' f x v‖ₑ = ‖v‖ₑ)
    (γ : ℝ → M) (hγ : MDifferentiable 𝓘(ℝ, ℝ) I γ) (a b : ℝ) :
    pathELength I' (f ∘ γ) a b = pathELength I γ a b := by
  simp only [pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro t
  have he := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I')
    t (hf (γ t)) (hγ t) (1 : TangentSpace 𝓘(ℝ, ℝ) t)
  rw [he]
  exact hnorm _ _

variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  [∀ x : M', ENormSMulClass ℝ (TangentSpace I' x)]

/-- Every tangent-norm-preserving smooth map decreases the actual path distance. -/
theorem riemannianEDist_map_le (f : M → M') (hf : ContMDiff I I' 1 f)
    (hnorm : ∀ x v, ‖mfderiv I I' f x v‖ₑ = ‖v‖ₑ) (x y : M) :
    riemannianEDist I' (f x) (f y) ≤ riemannianEDist I x y := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  have hle := riemannianEDist_le_pathELength (hf.comp hγ).contMDiffOn
    (congrArg f h0) (congrArg f h1) zero_le_one
  rw [pathELength_comp f (hf.mdifferentiable one_ne_zero) hnorm γ
    (hγ.mdifferentiable one_ne_zero)] at hle
  exact hle.trans_lt hlen

end TernaryPoly.RiemannianMapLength
