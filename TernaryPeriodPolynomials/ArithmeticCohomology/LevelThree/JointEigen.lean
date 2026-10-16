module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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
# Simultaneous eigenvectors of a commuting semisimple family

If `V` is a finite-dimensional complex vector space and `T i` (`i ∈ ι`) is a family of pairwise
commuting endomorphisms each of which is semisimple in the sense that its generalized eigenspaces
are eigenspaces, then `V` is the sum of the joint eigenspaces `⨅ i, eigenspace (T i) (χ i)`, and a
nonzero `V` has a joint eigenvector. This is the abstract form of the existence of Hecke
eigenforms in `S_k(Γ₁(3))`: the Hecke operators `T_p` (`p ≠ 3`) commute and are semisimple
(Petersson), so cusp forms are sums of joint eigenforms.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.LevelThree.JointEigen

open Module Module.End

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **A commuting semisimple family has joint eigenspaces spanning `V`.** -/
theorem iSup_iInf_eigenspace_eq_top (T : ι → End ℂ V)
    (hcomm : Pairwise fun i j => Commute (T i) (T j))
    (hss : ∀ i μ, (T i).maxGenEigenspace μ ≤ (T i).eigenspace μ) :
    ⨆ χ : ι → ℂ, ⨅ i, (T i).eigenspace (χ i) = ⊤ := by
  have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    T hcomm (fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i))
  refine eq_top_iff.mpr ?_
  rw [← h]
  exact iSup_mono fun χ => iInf_mono fun i => hss i (χ i)

/-- **A nonzero space carrying a commuting semisimple family has a joint eigenvector.** -/
theorem exists_joint_eigenvector [Nontrivial V] (T : ι → End ℂ V)
    (hcomm : Pairwise fun i j => Commute (T i) (T j))
    (hss : ∀ i μ, (T i).maxGenEigenspace μ ≤ (T i).eigenspace μ) :
    ∃ (χ : ι → ℂ) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  by_contra hcon
  have hbot : ⨆ χ : ι → ℂ, ⨅ i, (T i).eigenspace (χ i) = ⊥ := by
    refine iSup_eq_bot.mpr fun χ => ?_
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    exact hcon ⟨χ, v, hv0, fun i =>
      Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)⟩
  rw [iSup_iInf_eigenspace_eq_top T hcomm hss] at hbot
  exact top_ne_bot hbot

end TernaryPeriodPolynomials.LevelThree.JointEigen
