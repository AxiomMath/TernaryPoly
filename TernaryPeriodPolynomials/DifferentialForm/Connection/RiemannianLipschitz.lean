module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
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
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
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

/-! Quantitative control of the actual intrinsic metric by derivatives on convex coordinate domains. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Manifold MeasureTheory Metric Set Bundle
open scoped ContDiff Manifold Bundle ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [EMetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace


/-- A derivative bound on a convex open coordinate set controls genuine Riemannian distances. -/
theorem lipschitzOnWith_of_norm_mfderiv_le {U : Set F} (hU : IsOpen U) (hc : Convex ℝ U)
    {f : F → M} (hf : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 f U) {K : ℝ≥0}
    (hb : ∀ x ∈ U, ∀ v : F, ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f x v‖ₑ ≤ (K : ℝ≥0∞) * ‖v‖ₑ) :
    LipschitzOnWith K f U := by
  intro x hx y hy
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have hη : Set.MapsTo η (Icc (0 : ℝ) 1) U := by
    change Icc (0 : ℝ) 1 ⊆ η ⁻¹' U
    rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
    exact hc.segment_subset hx hy
  have hηsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 η (Icc (0 : ℝ) 1) := by
    exact (contMDiff_iff_contDiff.mpr η.contDiff).contMDiffOn
  have hlen : edist (f x) (f y) ≤ pathELength 𝓘(ℝ, E) (f ∘ η) 0 1 := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, E))]
    apply riemannianEDist_le_pathELength (hf.comp hηsmooth hη)
    · simp [η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [η, ContinuousAffineMap.coe_lineMap_eq]
    · exact zero_le_one
  apply hlen.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hd := (hf (η t) (hη ht)).mdifferentiableWithinAt one_ne_zero
  have he : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f ∘ η) (Icc (0 : ℝ) 1) t =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f (η t)) ∘L
        mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (Icc (0 : ℝ) 1) t := by
    rw [← mfderivWithin_of_mem_nhds (hU.mem_nhds (hη ht))]
    apply mfderivWithin_comp
    · exact hd
    · exact hηsmooth.mdifferentiableOn one_ne_zero t ht
    · exact hη
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  rw [he, ContinuousLinearMap.comp_apply]
  convert! hb (η t) (hη ht)
    (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (Icc (0 : ℝ) 1) t 1) using 1
  rw [mfderivWithin_eq_fderivWithin]
  rfl

end TernaryPoly.PolynomialFormConnection
