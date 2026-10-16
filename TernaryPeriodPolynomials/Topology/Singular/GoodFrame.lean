module

public import TernaryPeriodPolynomials.Building.Good.IntegralFrames
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularGoodFrame

open ModThreeGoodAction GoodLatticeReduction GoodIntegralFrames
open GoodIncidenceConnected GoodApartmentCycles

/-- The actual rational span of the three columns of an integral matrix. -/
def columnSpan (M : Matrix (Fin 3) (Fin 3) ℤ) : ModThreeGoodAction.RationalSubspace :=
  Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).col)

/-- Rational column independence is exactly nonsingularity of the original integer matrix. -/
theorem column_independent_iff_det_ne_zero (M : Matrix (Fin 3) (Fin 3) ℤ) :
    LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).col ↔ M.det ≠ 0 := by
  rw [Matrix.linearIndependent_cols_iff_isUnit,Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  have he : (M.map (Int.castRingHom ℚ)).det = (M.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det M).symm
  rw [he]
  exact Int.cast_ne_zero

/-- A singular frame spans at most a rational plane. -/
theorem columnSpan_finrank_le_two (M : Matrix (Fin 3) (Fin 3) ℤ) (hd : M.det = 0) :
    Module.finrank ℚ (columnSpan M) ≤ 2 := by
  have hn : ¬LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).col := by
    rw [column_independent_iff_det_ne_zero]
    exact not_not.mpr hd
  have hlt := Nat.lt_of_not_ge (mt linearIndependent_iff_card_le_finrank_span.mpr hn)
  change Module.finrank ℚ (columnSpan M) < 3 at hlt
  exact Nat.le_of_lt_succ hlt

/-- Every normalized column line is contained in the full rational column span. -/
theorem columnLine_le_columnSpan (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : NormalizedColumns M)
    (j : Fin 3) : (columnLine M hM j).val ≤ columnSpan M := by
  change Submodule.span ℚ {rationalVector (fun i => M i j)} ≤ columnSpan M
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl
  exact Submodule.subset_span ⟨j,rfl⟩

/-- The apartment of a singular normalized integral frame vanishes in the actual incidence kernel. -/
theorem frameApartment_eq_zero_of_det_eq_zero (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : NormalizedColumns M) (hd : M.det = 0) : frameApartment M hM = 0 := by
  classical
  by_cases he : columnLine M hM 0 = columnLine M hM 1
  · apply Subtype.ext
    change apartmentChain Good (columnLine M hM 0) (columnLine M hM 1) (columnLine M hM 2) = 0
    rw [he,apartmentChain,lineChain_self,lineChain_reverse Good (columnLine M hM 1) (columnLine M hM 2)]
    simp
  · let P : Plane Good := spanPlane Good (columnLine M hM 0) (columnLine M hM 1) he
    have hPS : P.val ≤ columnSpan M :=
      sup_le (columnLine_le_columnSpan M hM 0) (columnLine_le_columnSpan M hM 1)
    have hPeq : P.val = columnSpan M := by
      apply Submodule.eq_of_le_of_finrank_le hPS
      rw [P.property.1]
      exact columnSpan_finrank_le_two M hd
    exact apartmentCycle_collinear Good _ _ _ P
      (line_le_spanPlane_left Good _ _ he) (line_le_spanPlane_right Good _ _ he)
      (by rw [hPeq]; exact columnLine_le_columnSpan M hM 2)

end TernaryPoly.SingularGoodFrame
