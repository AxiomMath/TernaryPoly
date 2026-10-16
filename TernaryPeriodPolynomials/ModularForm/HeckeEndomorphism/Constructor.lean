module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
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
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm
namespace TernaryPoly.BinaryCuspHeckeEndomorphism

/-- Actual full-level slash invariance and vanishing at infinity give vanishing at every cusp. -/
def cuspOfInvariant (k : ℤ) (f : ℍ → ℂ)
    (hinv : ∀ g : SL(2, ℤ), f ∣[k] g = f)
    (hholo : MDiff f) (hzero : IsZeroAtImInfty f) : CuspForm 𝒮ℒ k where
  toFun := f
  slash_action_eq' g hg := by
    obtain ⟨g,rfl⟩ := hg
    exact hinv g
  holo' := hholo
  zero_at_cusps' hc := by
    apply (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr
    intro g _
    rw [hinv]
    exact hzero

@[simp] theorem cuspOfInvariant_apply (k : ℤ) (f : ℍ → ℂ)
    (hinv : ∀ g : SL(2, ℤ), f ∣[k] g = f)
    (hholo : MDiff f) (hzero : IsZeroAtImInfty f) (z : ℍ) :
    cuspOfInvariant k f hinv hholo hzero z = f z := rfl

end TernaryPoly.BinaryCuspHeckeEndomorphism
