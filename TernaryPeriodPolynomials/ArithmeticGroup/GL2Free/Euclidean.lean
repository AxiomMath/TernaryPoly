module

public import Mathlib.Data.Int.ModEq
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Control.Basic
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

@[expose] public section


namespace TernaryPoly.IntegralGL2Free

lemma even_reduction_pos (a b : ℤ) (hb : 0<b) (hab : a%2≠b%2) :
    ∃ k : ℤ, |a+2*k*b| < b := by
  let k := -((a+b)/(2*b))
  have hr0 := Int.emod_nonneg (a+b) (show 2*b≠0 by omega)
  have hr1 := Int.emod_lt_of_pos (a+b) (show 0<2*b by omega)
  have he := Int.emod_add_mul_ediv (a+b) (2*b)
  have hk : a+2*k*b=(a+b)%(2*b)-b := by dsimp [k]; nlinarith [he]
  refine ⟨k, ?_⟩
  rw [abs_lt]
  have hlo : -b≤a+2*k*b := by omega
  have hne : a+2*k*b≠-b := by
    rw [mul_assoc]
    omega
  exact ⟨lt_of_le_of_ne hlo hne.symm,by omega⟩

/-- Opposite parities remove the boundary case in nearest even division. -/
lemma even_reduction (a b : ℤ) (hb : b≠0) (hab : a%2≠b%2) :
    ∃ k : ℤ, |a+2*k*b| < |b| := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · have hab' : a%2≠(-b)%2 := by omega
    obtain ⟨k,hk⟩ := even_reduction_pos a (-b) (by omega) hab'
    refine ⟨-k, ?_⟩
    rw [abs_of_neg hb]
    convert hk using 1; congr 1; ring
  · simpa only [abs_of_pos hb] using even_reduction_pos a b hb hab

end TernaryPoly.IntegralGL2Free
