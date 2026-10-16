module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Actual compact smooth test transport along a genuine smooth homeomorphism. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set
open scoped ContDiff Distributions
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal image open set, written as the inverse map's preimage. -/
def transportedTestDomain (h : E ≃ₜ F) (Ω : TopologicalSpace.Opens E) : TopologicalSpace.Opens F :=
  ⟨h.symm ⁻¹' (Ω : Set E), Ω.isOpen.preimage h.symm.continuous⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Pulling a compactly supported function through a homeomorphism preserves actual compact support. -/
theorem tsupport_comp_homeomorph (h : E ≃ₜ F) {f : F → ℝ} (hf : HasCompactSupport f) :
    tsupport (fun x => f (h x)) ⊆ h.symm '' tsupport f := by
  apply closure_minimal _ (hf.image h.symm.continuous).isClosed
  intro x hx
  exact ⟨h x, subset_tsupport f hx, h.symm_apply_apply x⟩

/-- A genuine smooth homeomorphism with smooth inverse gives an actual equivalence of compact tests.
This declaration makes no assertion about transforming scalar currents as geometric densities. -/
def smoothTestEquiv (h : E ≃ₜ F) (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ h.symm)
    (Ω : TopologicalSpace.Opens E) : 𝓓(Ω, ℝ) ≃ₗ[ℝ] 𝓓(transportedTestDomain h Ω, ℝ) where
  toFun f :=
    { toFun := fun y => f (h.symm y)
      contDiff' := f.contDiff.comp hi
      hasCompactSupport' := (f.hasCompactSupport.image h.continuous).of_isClosed_subset
        (isClosed_tsupport _) (tsupport_comp_homeomorph h.symm f.hasCompactSupport)
      tsupport_subset' := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := tsupport_comp_homeomorph h.symm f.hasCompactSupport hy
        change h.symm (h x) ∈ (Ω : Set E)
        simpa only [h.symm_apply_apply] using f.tsupport_subset hx }
  invFun g :=
    { toFun := fun x => g (h x)
      contDiff' := g.contDiff.comp hh
      hasCompactSupport' := (g.hasCompactSupport.image h.symm.continuous).of_isClosed_subset
        (isClosed_tsupport _) (tsupport_comp_homeomorph h g.hasCompactSupport)
      tsupport_subset' := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := tsupport_comp_homeomorph h g.hasCompactSupport hx
        exact g.tsupport_subset hy }
  left_inv f := by
    apply TestFunction.ext
    intro x
    exact congrArg f (h.symm_apply_apply x)
  right_inv g := by
    apply TestFunction.ext
    intro y
    exact congrArg g (h.apply_symm_apply y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem smoothTestEquiv_apply (h : E ≃ₜ F) (hh : ContDiff ℝ ∞ h)
    (hi : ContDiff ℝ ∞ h.symm) (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(Ω, ℝ)) (y : F) : smoothTestEquiv h hh hi Ω f y = f (h.symm y) := rfl

@[simp] theorem smoothTestEquiv_symm_apply (h : E ≃ₜ F) (hh : ContDiff ℝ ∞ h)
    (hi : ContDiff ℝ ∞ h.symm) (Ω : TopologicalSpace.Opens E)
    (g : 𝓓(transportedTestDomain h Ω, ℝ)) (x : E) :
    (smoothTestEquiv h hh hi Ω).symm g x = g (h x) := rfl

end TernaryPoly.PolynomialFormWeakSmooth
