module

public import TernaryPeriodPolynomials.Building.FreeResolution.Lines
public import Mathlib.Basic.Complex.Basic

@[expose] public section


/-!
# Insertion signs

Original work by Claude Opus 5.5.

Simplices of the Voronoi complex are oriented by the labels of their lines: inserting a line `w`
into a set `T` costs the sign `(-1) ^ #{t ∈ T | label t < label w}`. Two insertions in either
order give opposite signs, which is `δ ∘ δ = 0` for the coboundary.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

/-- The sign of inserting a line into a set of lines. -/
def insSign (T : Finset Line) (w : Line) : ℂ :=
  (-1) ^ ((T.image Line.label).filter (· < w.label)).card

theorem insSign_sq (T : Finset Line) (w : Line) : insSign T w * insSign T w = 1 := by
  rw [insSign, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Inserting two lines with distinct labels in the two orders gives opposite signs. -/
theorem insSign_swap (T : Finset Line) {w w' : Line} (hw : w.label ∉ T.image Line.label)
    (hw' : w'.label ∉ T.image Line.label) (hne : w.label ≠ w'.label) :
    insSign T w * insSign (insert w T) w' = -(insSign T w' * insSign (insert w' T) w) := by
  have himg : ∀ u : Line, (insert u T).image Line.label = insert u.label (T.image Line.label) :=
    fun u => Finset.image_insert _ _ _
  unfold insSign
  rw [himg, himg, Finset.filter_insert, Finset.filter_insert]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h.le), Finset.card_insert_of_notMem]
    · rw [pow_succ]
      ring
    · intro hmem
      exact hw (Finset.mem_filter.mp hmem).1
  · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_left h, Finset.card_insert_of_notMem]
    · rw [pow_succ]
      ring
    · intro hmem
      exact hw' (Finset.mem_filter.mp hmem).1

end TernaryPeriodPolynomials.FreeResolution
