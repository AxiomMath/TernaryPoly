module

public import TernaryPeriodPolynomials.Building.Good.IncidenceConnected
public import TernaryPeriodPolynomials.Building.BipartitePathChains

@[expose] public section

noncomputable section
namespace TernaryPoly.GoodApartmentCycles
open GoodIncidenceConnected

variable (Good : RationalSubspace → Prop)

/-- The actual strict line-plane incidence relation. -/
abbrev Incidence (L : Line Good) (P : Plane Good) : Prop := L.val < P.val
abbrev Chains := BipartitePathChains.Chain₁ (Incidence Good)
abbrev Vertices := BipartitePathChains.Chain₀ (Line Good) (Plane Good)
abbrev boundary : Chains Good →ₗ[ℚ] Vertices Good := BipartitePathChains.boundary (Incidence Good)
abbrev Cycles := LinearMap.ker (boundary Good)

/-- A positively oriented flag from a line to a plane containing it. -/
def flagChain (L : Line Good) (P : Plane Good) (h : L.val ≤ P.val) : Chains Good :=
  Finsupp.single ⟨(L, P), line_lt_plane Good h⟩ 1

@[simp] theorem boundary_flagChain (L : Line Good) (P : Plane Good) (h : L.val ≤ P.val) :
    boundary Good (flagChain Good L P h) =
      Finsupp.single (.inr P) 1 - Finsupp.single (.inl L) 1 :=
  BipartitePathChains.boundary_single _ _ _

/-- Distinct lines determine the unique plane containing both. -/
theorem spanPlane_eq_of_common_plane (L M : Line Good) (hne : L ≠ M)
    (P : Plane Good) (hL : L.val ≤ P.val) (hM : M.val ≤ P.val) :
    spanPlane Good L M hne = P := by
  apply Subtype.ext
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hL hM)
    ((spanPlane Good L M hne).property.1.trans P.property.1.symm)

theorem line_le_spanPlane_left (L M : Line Good) (h : L ≠ M) :
    L.val ≤ (spanPlane Good L M h).val := le_sup_left

theorem line_le_spanPlane_right (L M : Line Good) (h : L ≠ M) :
    M.val ≤ (spanPlane Good L M h).val := le_sup_right

/-- The canonical two-edge chain from one good line to another. -/
def lineChain (L M : Line Good) : Chains Good := by
  classical
  exact if h : L = M then 0 else
    flagChain Good L (spanPlane Good L M h) (line_le_spanPlane_left Good L M h) -
      flagChain Good M (spanPlane Good L M h) (line_le_spanPlane_right Good L M h)

@[simp] theorem lineChain_self (L : Line Good) : lineChain Good L L = 0 := by
  classical
  exact dite_eq_left rfl

theorem lineChain_of_ne (L M : Line Good) (h : L ≠ M) :
    lineChain Good L M =
      flagChain Good L (spanPlane Good L M h) (line_le_spanPlane_left Good L M h) -
        flagChain Good M (spanPlane Good L M h) (line_le_spanPlane_right Good L M h) := by
  classical
  exact dite_eq_right h

/-- The canonical chain can be computed in any common plane, including equal lines. -/
theorem lineChain_of_common_plane (L M : Line Good) (P : Plane Good)
    (hL : L.val ≤ P.val) (hM : M.val ≤ P.val) :
    lineChain Good L M = flagChain Good L P hL - flagChain Good M P hM := by
  classical
  by_cases h : L = M
  · subst M
    rw [lineChain_self, sub_self]
  · rw [lineChain_of_ne Good L M h]
    have hp := spanPlane_eq_of_common_plane Good L M h P hL hM
    subst P
    rfl

/-- The line-chain boundary has exactly the expected endpoints. -/
theorem boundary_lineChain (L M : Line Good) :
    boundary Good (lineChain Good L M) =
      Finsupp.single (.inl M) 1 - Finsupp.single (.inl L) 1 := by
  classical
  by_cases h : L = M
  · subst M
    rw [lineChain_self, map_zero, sub_self]
  · rw [lineChain_of_ne Good L M h, map_sub, boundary_flagChain, boundary_flagChain]
    abel

/-- Reversing the two-line chain reverses its orientation. -/
theorem lineChain_reverse (L M : Line Good) : lineChain Good M L = -lineChain Good L M := by
  classical
  by_cases h : L = M
  · subst M
    rw [lineChain_self, neg_zero]
  · rw [lineChain_of_common_plane Good M L (spanPlane Good L M h) (line_le_spanPlane_right Good L M h) (line_le_spanPlane_left Good L M h),
      lineChain_of_common_plane Good L M (spanPlane Good L M h) (line_le_spanPlane_left Good L M h) (line_le_spanPlane_right Good L M h)]
    abel

/-- The literal oriented apartment chain of a triple of good rational lines. -/
def apartmentChain (L M N : Line Good) : Chains Good :=
  lineChain Good L M + lineChain Good M N + lineChain Good N L

@[simp] theorem boundary_apartmentChain (L M N : Line Good) :
    boundary Good (apartmentChain Good L M N) = 0 := by
  rw [apartmentChain, map_add, map_add, boundary_lineChain, boundary_lineChain, boundary_lineChain]
  abel

/-- The apartment is an element of the actual incidence boundary kernel. -/
def apartmentCycle (L M N : Line Good) : Cycles Good :=
  ⟨apartmentChain Good L M N, boundary_apartmentChain Good L M N⟩

@[simp] theorem apartmentCycle_coe (L M N : Line Good) :
    (apartmentCycle Good L M N : Chains Good) = apartmentChain Good L M N := rfl

/-- Cyclically rotating the lines preserves their oriented apartment chain. -/
theorem apartmentChain_cyclic (L M N : Line Good) :
    apartmentChain Good M N L = apartmentChain Good L M N := by
  unfold apartmentChain
  abel

/-- Interchanging two lines reverses the apartment orientation. -/
theorem apartmentChain_swap (L M N : Line Good) :
    apartmentChain Good M L N = -apartmentChain Good L M N := by
  unfold apartmentChain
  rw [lineChain_reverse Good L M, lineChain_reverse Good M N, lineChain_reverse Good N L]
  abel

/-- Three lines in a common rational plane have zero apartment chain. -/
theorem apartmentChain_collinear (L M N : Line Good) (P : Plane Good)
    (hL : L.val ≤ P.val) (hM : M.val ≤ P.val) (hN : N.val ≤ P.val) :
    apartmentChain Good L M N = 0 := by
  rw [apartmentChain, lineChain_of_common_plane Good L M P hL hM,
    lineChain_of_common_plane Good M N P hM hN, lineChain_of_common_plane Good N L P hN hL]
  abel

/-- The literal four-line apartment relation follows by cancellation of oriented edges. -/
theorem apartmentChain_four (L M N T : Line Good) :
    apartmentChain Good M N T - apartmentChain Good L N T +
      apartmentChain Good L M T - apartmentChain Good L M N = 0 := by
  unfold apartmentChain
  rw [lineChain_reverse Good M T, lineChain_reverse Good L N]
  abel

theorem apartmentCycle_cyclic (L M N : Line Good) :
    apartmentCycle Good M N L = apartmentCycle Good L M N := by
  apply Subtype.ext
  exact apartmentChain_cyclic Good L M N

theorem apartmentCycle_swap (L M N : Line Good) :
    apartmentCycle Good M L N = -apartmentCycle Good L M N := by
  apply Subtype.ext
  exact apartmentChain_swap Good L M N

theorem apartmentCycle_collinear (L M N : Line Good) (P : Plane Good)
    (hL : L.val ≤ P.val) (hM : M.val ≤ P.val) (hN : N.val ≤ P.val) :
    apartmentCycle Good L M N = 0 := by
  apply Subtype.ext
  exact apartmentChain_collinear Good L M N P hL hM hN

theorem apartmentCycle_four (L M N T : Line Good) :
    apartmentCycle Good M N T - apartmentCycle Good L N T +
      apartmentCycle Good L M T - apartmentCycle Good L M N = 0 := by
  apply Subtype.ext
  exact apartmentChain_four Good L M N T

end TernaryPoly.GoodApartmentCycles
