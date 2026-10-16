module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Ring.Pow
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


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryCharts

abbrev HalfLine := {r : ℝ // 0≤r}
abbrev Quadrant := HalfLine × HalfLine
abbrev HalfPlane := ℝ × HalfLine

/-- Recover the first coordinate from difference and minimum. -/
theorem max_sub_add_min (s t : ℝ) : max (s-t) 0+min s t=s := by
  simp only [max_def,min_def]
  split_ifs <;> linarith

theorem max_neg_sub_add_min (s t : ℝ) : max (-(s-t)) 0+min s t=t := by
  simp only [max_def,min_def]
  split_ifs <;> linarith

theorem max_sub_max_neg (x : ℝ) : max x 0-max (-x) 0=x := by
  simp only [max_def]
  split_ifs <;> linarith

theorem min_max_add (x r : ℝ) : min (max x 0+r) (max (-x) 0+r)=r := by
  simp only [min_def,max_def]
  split_ifs <;> linarith

/-- The closed quadrant is topologically a half-plane. No smoothness is asserted. -/
def quadrantHomeomorph : Quadrant ≃ₜ HalfPlane where
  toFun p := (p.1.val-p.2.val,⟨min p.1.val p.2.val,le_min p.1.property p.2.property⟩)
  invFun p := (⟨max p.1 0+p.2.val,add_nonneg (le_max_right _ _) p.2.property⟩,
    ⟨max (-p.1) 0+p.2.val,add_nonneg (le_max_right _ _) p.2.property⟩)
  left_inv p := by
    apply Prod.ext <;> apply Subtype.ext
    · exact max_sub_add_min _ _
    · exact max_neg_sub_add_min _ _
  right_inv p := by
    apply Prod.ext
    · change max p.1 0+p.2.val-(max (-p.1) 0+p.2.val)=p.1
      linarith [max_sub_max_neg p.1]
    · apply Subtype.ext
      exact min_max_add _ _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem quadrantHomeomorph_height (p : Quadrant) :
    (quadrantHomeomorph p).2.val=min p.1.val p.2.val := rfl

@[simp] theorem quadrantHomeomorph_positive (p : Quadrant) :
    0<(quadrantHomeomorph p).2.val ↔ 0<p.1.val ∧ 0<p.2.val := by
  exact lt_min_iff

@[simp] theorem quadrantHomeomorph_zero (p : Quadrant) :
    (quadrantHomeomorph p).2.val=0 ↔ p.1.val=0 ∨ p.2.val=0 := by
  change min p.1.val p.2.val=0 ↔ _
  constructor
  · intro h
    rcases min_choice p.1.val p.2.val with he|he
    · exact Or.inl (he.symm.trans h)
    · exact Or.inr (he.symm.trans h)
  · rintro (h|h)
    · rw [h,min_eq_left p.2.property]
    · rw [h,min_eq_right p.1.property]

end TernaryPoly.SymmetricSpaceBoundaryCharts
