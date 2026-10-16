module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Concrete square-norm bounds in a genuine finite coordinate system. -/
noncomputable section
namespace TernaryPoly.FiniteCoordinateSquare
variable {I F : Type*} [Fintype I] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pi_norm_square_le (u : I → ℝ) : ‖u‖ ^ 2 ≤ ∑ i, ‖u i‖ ^ 2 := by
  have hs : 0 ≤ ∑ i, ‖u i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h : ‖u‖ ≤ Real.sqrt (∑ i, ‖u i‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi := Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, ‖u i‖ ^ 2), norm_nonneg (u i)]
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, ‖u i‖ ^ 2), norm_nonneg u]

theorem square_le_coordinates (e : F ≃L[ℝ] (I → ℝ)) (u : F) :
    ‖u‖ ^ 2 ≤ ‖e.symm.toContinuousLinearMap‖ ^ 2 * ∑ i, ‖e u i‖ ^ 2 := by
  have h := e.symm.toContinuousLinearMap.le_opNorm (e u)
  change ‖e.symm (e u)‖ ≤ _ at h
  rw [e.symm_apply_apply] at h
  have hsq : ‖u‖ ^ 2 ≤ ‖e.symm.toContinuousLinearMap‖ ^ 2 * ‖e u‖ ^ 2 := by
    nlinarith [norm_nonneg u, norm_nonneg (e u), norm_nonneg e.symm.toContinuousLinearMap]
  exact hsq.trans (mul_le_mul_of_nonneg_left (pi_norm_square_le (e u)) (sq_nonneg _))

theorem coordinates_le_square (e : F ≃L[ℝ] (I → ℝ)) (u : F) :
    ∑ i, ‖e u i‖ ^ 2 ≤ (Fintype.card I : ℝ) * ‖e.toContinuousLinearMap‖ ^ 2 * ‖u‖ ^ 2 := by
  calc
    _ ≤ ∑ _i : I, ‖e.toContinuousLinearMap‖ ^ 2 * ‖u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (norm_le_pi_norm (e u) i).trans (e.toContinuousLinearMap.le_opNorm u)
      nlinarith [norm_nonneg (e u i), norm_nonneg u, norm_nonneg e.toContinuousLinearMap]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

end TernaryPoly.FiniteCoordinateSquare
