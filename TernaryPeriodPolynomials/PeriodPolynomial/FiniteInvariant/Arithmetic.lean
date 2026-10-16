module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
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


noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

/-- The rational trace expression is the integer odd-symmetric monomial count. -/
theorem odd_count_arithmetic (d : ℕ) (hd : Even d) :
    (1/4 : ℚ)*((d+1 : ℕ)-(-1 : ℚ)^(d/2)) = ((d+2)/4 : ℕ) := by
  have he : d%2=0 := Nat.even_iff.mp hd
  have hm : d%4=0 ∨ d%4=2 := by omega
  rw [neg_one_pow_eq_pow_mod_two]
  rcases hm with hm | hm
  · have hq : d/2%2=0 := by omega
    rw [hq]
    norm_num
    have h : 4*((d+2)/4)=d := by omega
    have hc : (4 : ℚ)*(((d+2)/4 : ℕ) : ℚ)=d := by exact_mod_cast h
    linarith
  · have hq : d/2%2=1 := by omega
    rw [hq]
    norm_num
    have h : 4*((d+2)/4)=d+2 := by omega
    have hc : (4 : ℚ)*(((d+2)/4 : ℕ) : ℚ)=(d : ℚ)+2 := by exact_mod_cast h
    linarith

/-- The rational invariant character expression is the integer degree-six count. -/
theorem invariant_count_arithmetic (d : ℕ) (hd : Even d) :
    (1/6 : ℚ)*((d+4 : ℕ)+2*(if d%3=0 then 1 else if d%3=1 then -1 else 0)) =
      (d/6+1 : ℕ) := by
  have he : d%2=0 := Nat.even_iff.mp hd
  have hm : d%6=0 ∨ d%6=2 ∨ d%6=4 := by omega
  rcases hm with hm | hm | hm
  · have h3 : d%3=0 := by omega
    simp only [h3,ite_true]
    have h : 6*(d/6)=d := by omega
    have hc : (6 : ℚ)*((d/6 : ℕ) : ℚ)=d := by exact_mod_cast h
    push_cast
    linarith
  · have h3 : d%3=2 := by omega
    norm_num [h3]
    have h : 6*(d/6)+2=d := by omega
    have hc : (6 : ℚ)*((d/6 : ℕ) : ℚ)+2=d := by exact_mod_cast h
    linarith
  · have h3 : d%3=1 := by omega
    norm_num [h3]
    have h : 6*(d/6)+4=d := by omega
    have hc : (6 : ℚ)*((d/6 : ℕ) : ℚ)+4=d := by exact_mod_cast h
    linarith

end TernaryPoly.BinaryFiniteInvariant
