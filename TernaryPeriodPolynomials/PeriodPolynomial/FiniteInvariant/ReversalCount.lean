module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

/-- In even degree reversal has exactly the middle bounded exponent as a fixed point. -/
theorem sum_reversal_fixed (d : ℕ) (hd : Even d) (w : Fin (d+1) → ℚ) :
    (∑ i : Fin (d+1), w i * ((Pi.single i.rev (1 : ℚ) : Fin (d+1) → ℚ) i)) = w ⟨d/2,by omega⟩ := by
  classical
  let j : Fin (d+1) := ⟨d/2,by omega⟩
  have hrev (i : Fin (d+1)) : i.rev=i ↔ i=j := by
    obtain ⟨k,hk⟩ := hd
    constructor
    · intro hi
      apply Fin.ext
      have hv := congrArg Fin.val hi
      rw [Fin.val_rev] at hv
      change i.val=d/2
      omega
    · intro hi
      subst i
      apply Fin.ext
      rw [Fin.val_rev]
      change d+1-(d/2+1)=d/2
      omega
  rw [Finset.sum_eq_single j]
  · rw [(hrev j).mpr rfl]
    simp [j]
  · intro i _ hi
    have hni : i.rev ≠ i := (hrev i).not.mpr hi
    simp [Ne.symm hni]
  · simp

end TernaryPoly.BinaryFiniteInvariant
