module

public import TernaryPeriodPolynomials.Building.Good.FrameSubdivision
public import TernaryPeriodPolynomials.Building.Good.DeterminantDescent
public import TernaryPeriodPolynomials.Topology.Singular.GoodFrame
public import TernaryPeriodPolynomials.Building.Good.ApartmentSpan

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodUnimodularSpan
open ModThreeGoodAction GoodLatticeReduction GoodDeterminantDescent
open GoodIncidenceConnected GoodApartmentCycles GoodIntegralFrames SingularGoodFrame

abbrev UnimodularFrame := {M : Matrix (Fin 3) (Fin 3) ℤ //
  NormalizedColumns M ∧ M.det.natAbs = 1}

/-- The span of actual normalized unimodular apartments inside the true cycle module. -/
def unimodularSpan : Submodule ℚ (GoodApartmentCycles.Cycles Good) :=
  Submodule.span ℚ (Set.range (fun M : UnimodularFrame => frameApartment M.val M.property.1))

/-- Strict determinant descent expresses every integral normalized frame in the unimodular span. -/
theorem frameApartment_mem (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : NormalizedColumns M) :
    frameApartment M hM ∈ unimodularSpan := by
  generalize hn : M.det.natAbs = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hz : M.det = 0
    · rw [frameApartment_eq_zero_of_det_eq_zero M hM hz]
      exact unimodularSpan.zero_mem
    by_cases h1 : M.det.natAbs = 1
    · exact Submodule.subset_span ⟨⟨M,hM,h1⟩,rfl⟩
    have h0 : M.det.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
    have hl : 1 < M.det.natAbs := by omega
    obtain ⟨w,hw,hu⟩ := exists_normalized_determinant_descent M hM hz hl
    rw [frameApartment_subdivision M hM w hw (fun j => (hu j).2)]
    apply unimodularSpan.add_mem
    · apply unimodularSpan.add_mem
      · exact ih _ (by simpa only [← hn] using (hu 0).1) _ (hu 0).2 rfl
      · exact ih _ (by simpa only [← hn] using (hu 1).1) _ (hu 1).2 rfl
    · exact ih _ (by simpa only [← hn] using (hu 2).1) _ (hu 2).2 rfl

/-- Every rational good apartment is in the normalized unimodular span. -/
theorem apartment_mem (L M N : Line Good) : apartmentCycle Good L M N ∈ unimodularSpan := by
  rw [apartment_eq_frame]
  exact frameApartment_mem _ _

/-- All cycles are spanned by normalized unimodular apartments, without a degree bound. -/
theorem unimodularSpan_eq_top : unimodularSpan = ⊤ := by
  have h : apartmentSpan Good ≤ unimodularSpan := by
    apply Submodule.span_le.mpr
    rintro c ⟨t,rfl⟩
    exact apartment_mem t.1 t.2.1 t.2.2
  rw [apartmentSpan_eq_top Good ⟨firstLine,firstLine_finrank,firstLine_good⟩] at h
  exact top_unique h

end TernaryPoly.GoodUnimodularSpan
