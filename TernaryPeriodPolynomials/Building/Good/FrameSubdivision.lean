module

public import TernaryPeriodPolynomials.Building.Good.IntegralFrames

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodIntegralFrames
open ModThreeGoodAction GoodLatticeReduction
open GoodIncidenceConnected GoodApartmentCycles

/-- The actual new column line is the line of the inserted integral vector. -/
theorem columnLine_updateCol_same (M : Matrix (Fin 3) (Fin 3) ℤ)
    (w : IntegralVector) (hw : ∑ i, (w i : ZMod 3) = 1) (j : Fin 3)
    (hU : NormalizedColumns (M.updateCol j w)) :
    columnLine (M.updateCol j w) hU j = vectorLine w hw := by
  apply Subtype.ext
  simp only [columnLine,vectorLine,Matrix.updateCol_apply,ite_true]

/-- Every other column line is literally unchanged. -/
theorem columnLine_updateCol_ne (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : NormalizedColumns M) (w : IntegralVector) (j k : Fin 3) (hjk : k ≠ j)
    (hU : NormalizedColumns (M.updateCol j w)) :
    columnLine (M.updateCol j w) hU k = columnLine M hM k := by
  apply Subtype.ext
  simp only [columnLine,vectorLine,Matrix.updateCol_apply,ite_eq_right hjk]

/-- The four-line relation expresses an apartment as the sum of the three replacements. -/
theorem apartmentCycle_subdivision (L M N W : Line Good) :
    apartmentCycle Good L M N = apartmentCycle Good W M N +
      apartmentCycle Good L W N + apartmentCycle Good L M W := by
  have h := sub_eq_zero.mp (apartmentCycle_four Good L M N W)
  have hs : apartmentCycle Good L W N = -apartmentCycle Good L N W :=
    (apartmentCycle_cyclic Good N L W).trans (apartmentCycle_swap Good L N W)
  rw [hs,← apartmentCycle_cyclic Good W M N]
  simpa only [sub_eq_add_neg] using h.symm

/-- The actual normalized frame apartment is the sum of its three column replacements. -/
theorem frameApartment_subdivision (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : NormalizedColumns M) (w : IntegralVector) (hw : ∑ i, (w i : ZMod 3) = 1)
    (hU : ∀ j, NormalizedColumns (M.updateCol j w)) :
    frameApartment M hM = frameApartment (M.updateCol 0 w) (hU 0) +
      frameApartment (M.updateCol 1 w) (hU 1) + frameApartment (M.updateCol 2 w) (hU 2) := by
  simp only [frameApartment,columnLine_updateCol_same M w hw]
  rw [columnLine_updateCol_ne M hM w 0 1 (by decide),
      columnLine_updateCol_ne M hM w 0 2 (by decide),
      columnLine_updateCol_ne M hM w 1 0 (by decide),
      columnLine_updateCol_ne M hM w 1 2 (by decide),
      columnLine_updateCol_ne M hM w 2 0 (by decide),
      columnLine_updateCol_ne M hM w 2 1 (by decide)]
  exact apartmentCycle_subdivision _ _ _ _

end TernaryPoly.GoodIntegralFrames
