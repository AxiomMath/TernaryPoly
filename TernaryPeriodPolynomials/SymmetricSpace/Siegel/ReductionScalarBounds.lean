module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
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
namespace TernaryPoly.SymmetricSpaceSiegelReduction

theorem square_le_quarter {x : ℝ} (hx : |x|≤1/2) : x^2≤1/4 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)]

/-- The two elementary successive-minimum inequalities give uniform simple-root bounds. -/
theorem root_bounds_of_minimum_inequalities (x y a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hx : |x|≤1/2) (hy : |y|≤1/2)
    (hlast : 1≤b+y^2) (hsecond : b≤a+x^2*b) :
    Real.sqrt (b/a)≤2 ∧ (Real.sqrt b)⁻¹≤2 := by
  have hxq := square_le_quarter hx
  have hyq := square_le_quarter hy
  have hxb := mul_le_mul_of_nonneg_right hxq hb.le
  have hab : b≤4*a := by nlinarith
  have hbb : (1 : ℝ)/4≤b := by nlinarith
  constructor
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    apply (div_le_iff₀ ha).mpr
    nlinarith
  · have hs : (1 : ℝ)/2≤Real.sqrt b := Real.le_sqrt_of_sq_le (by norm_num; exact hbb)
    apply (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hb)).mpr
    nlinarith

end TernaryPoly.SymmetricSpaceSiegelReduction
