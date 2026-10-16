module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! A bounded compact-core commutator and a genuine test transpose transport weak equations. -/
namespace TernaryPoly.BoundedWeakCommutatorTransport
variable {A B E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem transport (i : A → E) (j : B → F) (hi : DenseRange i) (hj : DenseRange j)
    (d : A → B) (δ : B → A) (τ : B → B)
    (R : F →L[ℝ] F) (V C : E →L[ℝ] F)
    (hpair : ∀ a b, inner ℝ (j (d a)) (j b) = inner ℝ (i a) (i (δ b)))
    (htranspose : ∀ y b, inner ℝ (R y) (j b) = inner ℝ y (j (τ b)))
    (hcore : ∀ a, V (i a) - C (i a) = R (j (d a)))
    (x : E) (z : F) (hweak : ∀ b, inner ℝ z (j b) = inner ℝ x (i (δ b))) :
    V x = R z + C x := by
  have htest (b : B) : inner ℝ (V x - C x) (j b) = inner ℝ x (i (δ (τ b))) := by
    refine hi.induction_on x ?_ ?_
    · exact isClosed_eq ((V.continuous.sub C.continuous).inner continuous_const)
        (continuous_id.inner continuous_const)
    intro a
    exact (congrArg (fun y : F => inner ℝ y (j b)) (hcore a)).trans
      ((htranspose (j (d a)) b).trans (hpair a (τ b)))
  have he : V x - C x = R z := by
    apply ext_inner_right ℝ
    intro y
    refine hj.induction_on y ?_ ?_
    · exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    intro b
    exact (htest b).trans ((hweak (τ b)).symm.trans (htranspose z b).symm)
  exact (sub_eq_iff_eq_add.mp he)

end TernaryPoly.BoundedWeakCommutatorTransport
