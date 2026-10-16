module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.Cell0Geometry

@[expose] public section


/-!
# Lemma B.1, boundary route: the neighbours of the standard top cell and of its two hexagons

The six minimal lines of each of the sixteen vertices of the standard top cell `T₀ = {e₀, e₁, e₂}` are tabulated
(`vtx16_M`); `nbrs_T0` is the exact set of ten lines whose insertion into `T₀` still gives a simplex, and
`nbrs_hexPlus`, `nbrs_hexMinus` those of the two hexagons `T₀ ∪ {e₁ ± e₂}` (six lines `(1, u)` each, occurring in the
pairs `±u`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.FreeResolution GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

/-- The six minimal vectors (up to sign) of each of the sixteen vertices of the standard top cell. -/
def tab : Fin 16 → Fin 6 → Vec :=
  ![![![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]],
   ![![0, 0, 1], ![0, 1, -1], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0]],
   ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]],
   ![![0, 0, 1], ![0, 1, -1], ![0, 1, 0], ![1, 0, 0], ![1, 1, -1], ![1, 1, 0]],
   ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, -1], ![1, 0, 0], ![1, 1, 0]],
   ![![0, 0, 1], ![0, 1, 0], ![1, 0, -1], ![1, 0, 0], ![1, 1, -1], ![1, 1, 0]],
   ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1]],
   ![![0, 0, 1], ![0, 1, -1], ![0, 1, 0], ![1, -1, 1], ![1, 0, 0], ![1, 0, 1]],
   ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, -1, -1], ![1, 0, -1], ![1, 0, 0]],
   ![![0, 0, 1], ![0, 1, -1], ![0, 1, 0], ![1, 0, -1], ![1, 0, 0], ![1, 1, -1]],
   ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, -1, 0], ![1, 0, 0], ![1, 0, 1]],
   ![![0, 0, 1], ![0, 1, 0], ![1, -1, 0], ![1, -1, 1], ![1, 0, 0], ![1, 0, 1]],
   ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, -1, -1], ![1, -1, 0], ![1, 0, 0]],
   ![![0, 0, 1], ![0, 1, -1], ![0, 1, 0], ![1, -1, 0], ![1, -1, 1], ![1, 0, 0]],
   ![![0, 0, 1], ![0, 1, 0], ![1, -1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, 0]],
   ![![0, 0, 1], ![0, 1, -1], ![0, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, 0]]]


theorem tab_qf (k : Fin 16) (i : Fin 6) :
    qf (gram3 (triples k).1 (triples k).2.1 (triples k).2.2) (tab k i) = 1 := by
  fin_cases k <;> fin_cases i <;> simp [qf, gram3, triples, tab, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> norm_num

theorem tab_distinct : ∀ k : Fin 16, ∀ i j : Fin 6, i ≠ j → tab k i ≠ tab k j ∧ tab k i ≠ -tab k j := by
  decide +kernel

theorem vtx16_M (k : Fin 16) : (vtx16 k).M = Finset.univ.image (fun i : Fin 6 => Line.mk (tab k i)) := by
  have hinj : Function.Injective (fun i : Fin 6 => Line.mk (tab k i)) := by
    intro i j h
    by_contra hne
    rcases Line.mk_eq_mk.mp h with h1 | h1
    · exact (tab_distinct k i j hne).1 h1.symm
    · exact (tab_distinct k i j hne).2 (by rw [h1, neg_neg])
  have hsub : Finset.univ.image (fun i : Fin 6 => Line.mk (tab k i)) ⊆ (vtx16 k).M := by
    intro ℓ hℓ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hℓ
    rw [Vtx.mem_M_mk]
    exact tab_qf k i
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Vtx.card_M, Finset.card_image_of_injective _ hinj]
  simp

theorem nbrs_eq_of_T0_sub (F : Finset Line) (hF : T0set ⊆ F) :
    nbrs F = ((Finset.univ.filter fun k : Fin 16 => F ⊆ (vtx16 k).M).biUnion
      fun k => (vtx16 k).M).filter (· ∉ F) := by
  have hsp : Spans F := T0_spans.mono hF
  unfold nbrs
  rw [dite_eq_left hsp]
  congr 1
  ext w
  simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, vertSet, Set.mem_ofPred_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, hw⟩
    have h1 : v ∈ vertFin T0 := (mem_vertFin T0 v).mpr (hF.trans hv)
    rw [vertFin_T0] at h1
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h1
    exact ⟨k, hv, hw⟩
  · rintro ⟨k, hk, hw⟩
    exact ⟨vtx16 k, hk, hw⟩

/-- The standard top cell with the line `e₁ + e₂` of the plane `x₀ = 0` added. -/
def hexPlusSet : Finset Line := insert (Line.mk ![0, 1, 1]) T0set

/-- The standard top cell with the line `e₁ - e₂` of the plane `x₀ = 0` added. -/
def hexMinusSet : Finset Line := insert (Line.mk ![0, 1, -1]) T0set

theorem nbrs_T0 : nbrs T0set = {Line.mk ![0, 1, 1], Line.mk ![0, 1, -1], Line.mk ![1, 1, 0],
    Line.mk ![1, -1, 0], Line.mk ![1, 0, 1], Line.mk ![1, 0, -1], Line.mk ![1, 1, 1], Line.mk ![1, 1, -1],
    Line.mk ![1, -1, 1], Line.mk ![1, -1, -1]} := by
  rw [nbrs_eq_of_T0_sub T0set subset_rfl]
  simp only [vtx16_M]
  decide +kernel

theorem nbrs_hexPlus : nbrs hexPlusSet = {Line.mk ![1, 1, 0], Line.mk ![1, -1, 0], Line.mk ![1, 0, 1],
    Line.mk ![1, 0, -1], Line.mk ![1, 1, 1], Line.mk ![1, -1, -1]} := by
  rw [hexPlusSet, nbrs_eq_of_T0_sub _ (Finset.subset_insert _ _)]
  simp only [vtx16_M]
  decide +kernel

theorem nbrs_hexMinus : nbrs hexMinusSet = {Line.mk ![1, 1, 0], Line.mk ![1, -1, 0], Line.mk ![1, 0, 1],
    Line.mk ![1, 0, -1], Line.mk ![1, 1, -1], Line.mk ![1, -1, 1]} := by
  rw [hexMinusSet, nbrs_eq_of_T0_sub _ (Finset.subset_insert _ _)]
  simp only [vtx16_M]
  decide +kernel

end TernaryPeriodPolynomials.Argument.AppendixBResidue
