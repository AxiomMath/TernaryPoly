module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.LinearAlgebra.Dual.Defs
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


/-! The faithful algebraic test-dual embedding of an inner-product completion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth

variable {V E : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pairing against a specified embedded test space. -/
def testEmbedding (i : V →ₗ[ℝ] E) : E →ₗ[ℝ] Module.Dual ℝ V where
  toFun u :=
    { toFun := fun b => inner ℝ u (i b)
      map_add' := by intro a b; rw [map_add, inner_add_right]
      map_smul' := by intro c b; simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro b
    exact inner_add_left _ _ _
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro b
    exact real_inner_smul_left _ _ _

@[simp] theorem testEmbedding_apply (i : V →ₗ[ℝ] E) (u : E) (b : V) :
    testEmbedding i u b = inner ℝ u (i b) := rfl

/-- A dense embedded test space separates all elements of the ambient inner-product space. -/
theorem testEmbedding_injective (i : V →ₗ[ℝ] E) (hi : DenseRange i) :
    Function.Injective (testEmbedding i) := by
  intro u v huv
  apply hi.eq_of_inner_left ℝ
  intro b
  exact congrArg (fun T : Module.Dual ℝ V => T b) huv

variable {W F : Type*} [AddCommGroup W] [Module ℝ W]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Equality after transposing a test operator is precisely equality of all its pairings. -/
theorem dualMap_testEmbedding_eq_iff (i : V →ₗ[ℝ] E) (j : W →ₗ[ℝ] F)
    (A : W →ₗ[ℝ] V) (u : E) (z : F) :
    A.dualMap (testEmbedding i u) = testEmbedding j z ↔
      ∀ b, inner ℝ z (j b) = inner ℝ u (i (A b)) := by
  constructor
  · intro h b
    exact (congrArg (fun T : Module.Dual ℝ W => T b) h).symm
  · intro h
    apply LinearMap.ext
    intro b
    exact (h b).symm

end TernaryPoly.PolynomialFormWeakSmooth
