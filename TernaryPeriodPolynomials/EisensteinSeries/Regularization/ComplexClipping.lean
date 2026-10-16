module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
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


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def complexClip (bound : ℝ) (value : ℂ) : ℂ :=
  ((max (-bound) (min bound value.re) : ℝ) : ℂ) +
    ((max (-bound) (min bound value.im) : ℝ) : ℂ) * Complex.I

theorem complexClip_continuous (bound : ℝ) : Continuous (complexClip bound) := by
  unfold complexClip
  fun_prop

theorem complexClip_norm_le {bound : ℝ} (nonnegative : 0 ≤ bound) (value : ℂ) :
    ‖complexClip bound value‖ ≤ 2 * bound := by
  have estimate (part : ℝ) : |max (-bound) (min bound part)| ≤ bound := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  calc
    _ ≤ |(complexClip bound value).re| + |(complexClip bound value).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ bound + bound := by simpa [complexClip] using add_le_add (estimate value.re) (estimate value.im)
    _ = _ := by ring

theorem complexClip_eq_self {bound : ℝ} {value : ℂ} (bounded : ‖value‖ ≤ bound) :
    complexClip bound value = value := by
  have real_bounds := abs_le.mp ((Complex.abs_re_le_norm value).trans bounded)
  have imag_bounds := abs_le.mp ((Complex.abs_im_le_norm value).trans bounded)
  simp only [complexClip, min_eq_right real_bounds.2, min_eq_right imag_bounds.2,
    max_eq_right real_bounds.1, max_eq_right imag_bounds.1]
  exact Complex.re_add_im value

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
