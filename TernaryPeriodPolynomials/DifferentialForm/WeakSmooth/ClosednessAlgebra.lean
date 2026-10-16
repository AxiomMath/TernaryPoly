module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Convex.PathConnected
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
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! A weak primitive is closed when tested against an actual adjoint complex. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth

variable {V W Z E F G : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The weak equation and the compact adjoint-complex identity force the smooth derivative to vanish. -/
theorem derivative_eq_zero_of_weak_primitive
    (i : V →ₗ[ℝ] E) (j : W →ₗ[ℝ] F) (l : Z →ₗ[ℝ] G)
    (hl : Function.Injective l) (T : W →ₗ[ℝ] Z)
    (A : W →ₗ[ℝ] V) (B : Z →ₗ[ℝ] W)
    (hT : ∀ w z, inner ℝ (l (T w)) (l z) = inner ℝ (j w) (j (B z)))
    (hC : ∀ z, A (B z) = 0) (w : W) (u : E)
    (hu : ∀ b, inner ℝ (j w) (j b) = inner ℝ u (i (A b))) : T w = 0 := by
  have hz : inner ℝ (l (T w)) (l (T w)) = 0 := by
    calc
      _ = inner ℝ (j w) (j (B (T w))) := hT w (T w)
      _ = inner ℝ u (i (A (B (T w)))) := hu (B (T w))
      _ = 0 := by rw [hC, map_zero, inner_zero_right]
  exact hl ((inner_self_eq_zero.mp hz).trans (map_zero l).symm)

end TernaryPoly.PolynomialFormWeakSmooth
