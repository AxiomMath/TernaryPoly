module

public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.ActionLinearization
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.Data.Fintype.Order
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory FreeActionLinearization

/-- A genuine invariant set cover of a group-set. In the singular application its points are
actual cover-small singular simplices and membership is literal containment in a cover member. -/
structure InvariantSetCover (G : Type) [Group G] (S : Type) [MulAction G S] (ι : Type) where
  mem : ι → S → Prop
  covers : ∀ s, ∃ i, mem i s
  invariant : ∀ (i : ι) (g : G) (s : S), mem i (g • s) ↔ mem i s

namespace InvariantSetCover
variable {G S ι : Type} [Group G] [MulAction G S] (U : InvariantSetCover G S ι)

/-- A covering member is selected on each actual orbit, ensuring invariance under the group. -/
def index (s : S) : ι := Classical.choose (U.covers (⟦s⟧ : Orbits G S).out)

/-- The selected index is genuinely invariant under the group action. -/
theorem index_smul (g : G) (s : S) : U.index (g • s) = U.index s := by
  simp [index]

/-- The selected cover member actually contains the given point. -/
theorem index_mem (s : S) : U.mem (U.index s) s := by
  obtain ⟨⟨q,g⟩,rfl⟩ := orbitProductMap_surjective G S s
  change U.mem (Classical.choose (U.covers (⟦orbitProductMap G S (q,g)⟧ : Orbits G S).out))
    (g • q.out)
  rw [orbitProductMap_orbit]
  exact (U.invariant _ g q.out).mpr (Classical.choose_spec (U.covers q.out))

/-- A genuine Čech flag consists of a point and an ordered tuple of cover members containing it. -/
@[ext] structure Flag (k : ℕ) where
  labels : Fin k → ι
  point : S
  membership : ∀ a, U.mem (labels a) point

/-- The actual group acts on the point of a Čech flag, preserving every cover label. -/
instance flagMulAction (k : ℕ) : MulAction G (U.Flag k) where
  smul g x := ⟨x.labels,g • x.point,fun a => (U.invariant (x.labels a) g x.point).mpr (x.membership a)⟩
  one_smul x := Flag.ext rfl (one_smul G x.point)
  mul_smul g h x := Flag.ext rfl (mul_smul g h x.point)

/-- Tuple selection is an actual equivariant map of Čech flags. -/
def select {p q : ℕ} (f : Fin p → Fin q) (x : U.Flag q) : U.Flag p :=
  ⟨x.labels ∘ f,x.point,fun a => x.membership (f a)⟩

/-- Selection commutes with the actual group action. -/
theorem select_smul {p q : ℕ} (f : Fin p → Fin q) (g : G) (x : U.Flag q) :
    U.select f (g • x) = g • U.select f x := rfl

/-- Prepending the actual invariant containing index provides the Čech contraction. -/
def prepend {k : ℕ} (x : U.Flag k) : U.Flag (k+1) :=
  ⟨Fin.cons (U.index x.point) x.labels,x.point,Fin.cases (U.index_mem x.point) x.membership⟩

/-- The chosen Čech contraction commutes with the actual group action. -/
theorem prepend_smul {k : ℕ} (g : G) (x : U.Flag k) : U.prepend (g • x) = g • U.prepend x := by
  apply Flag.ext
  · funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    exact U.index_smul g x.point
  · rfl

/-- Deleting the prepended cover member recovers the original actual flag. -/
theorem select_zero_prepend {k : ℕ} (x : U.Flag k) :
    U.select (0 : Fin (k+1)).succAbove (U.prepend x) = x := by
  apply Flag.ext
  · exact Fin.cons_comp_succ (U.index x.point) x.labels
  · rfl

/-- Every other deletion commutes with the actual invariant prepend operation. -/
theorem select_succ_prepend {k : ℕ} (i : Fin (k+1)) (x : U.Flag (k+1)) :
    U.select i.succ.succAbove (U.prepend x) = U.prepend (U.select i.succAbove x) := by
  apply Flag.ext
  · exact Fin.cons_comp_succ_succAbove _ _ i
  · rfl

end InvariantSetCover
end TernaryPoly.SmoothSingularGlobal
