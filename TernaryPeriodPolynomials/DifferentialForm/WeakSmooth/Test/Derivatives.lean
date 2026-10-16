module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
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


/-! Actual constant-direction derivatives of compact smooth tests commute. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped ContDiff Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiation of an actual first derivative applied to a fixed vector. -/
theorem lineDeriv_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    lineDeriv ℝ (fun y => fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  have hh := (contDiff_infty_iff_fderiv.mp hf).2
  have h := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x
    ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt)
  exact h.differentiableAt.lineDeriv_eq_fderiv.trans
    (congrArg (fun L : E →L[ℝ] ℝ => L u) h.fderiv)

/-- The actual bundled directional test derivative is the actual first Frechet derivative. -/
theorem testDerivative_eq_fderiv (Ω : TopologicalSpace.Opens E) (f : 𝓓(Ω, ℝ)) (v : E) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v f : E → ℝ) = fun x => fderiv ℝ f x v := by
  funext x
  rw [TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp)]
  exact (f.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv

/-- Schwarz symmetry gives commuting actual compact-test derivatives in arbitrary directions. -/
theorem testDerivative_commute (Ω : TopologicalSpace.Opens E) (f : 𝓓(Ω, ℝ)) (u v : E) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ u (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v f) =
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ u f) : 𝓓(Ω, ℝ)) := by
  apply TestFunction.ext
  intro x
  simp only [TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp)]
  rw [testDerivative_eq_fderiv, testDerivative_eq_fderiv]
  rw [lineDeriv_fderiv_apply f.contDiff, lineDeriv_fderiv_apply f.contDiff]
  exact (f.contDiff.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq u v

end TernaryPoly.PolynomialFormWeakSmooth
