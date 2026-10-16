module

public import TernaryPeriodPolynomials.Building.Good.ApartmentSpan
public import TernaryPeriodPolynomials.Building.Good.Building

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodApartmentCycles
open GoodIncidenceConnected

variable (Good : RationalSubspace → Prop)
variable (e : RationalSubspace ≃o RationalSubspace)
variable (hdim : ∀ L, Module.finrank ℚ (e L) = Module.finrank ℚ L)
variable (hgood : ∀ L, Good (e L) ↔ Good L)

theorem incidenceEquiv_iff (L : Line Good) (P : Plane Good) :
    Incidence Good L P ↔ Incidence Good (GoodBuilding.lineEquiv Good e hdim hgood L)
      (GoodBuilding.planeEquiv Good e hdim hgood P) := e.lt_iff_lt.symm

/-- The actual chain equivalence induced by a good, dimension-preserving subspace automorphism. -/
def apartmentChainEquiv : Chains Good ≃ₗ[ℚ] Chains Good :=
  BipartitePathChains.chainEquiv (GoodBuilding.lineEquiv Good e hdim hgood)
    (GoodBuilding.planeEquiv Good e hdim hgood) (incidenceEquiv_iff Good e hdim hgood)

/-- A positive incidence flag is sent to its actual image flag. -/
theorem apartmentChainEquiv_flag (L : Line Good) (P : Plane Good) (h : L.val ≤ P.val) :
    apartmentChainEquiv Good e hdim hgood (flagChain Good L P h) =
      flagChain Good (GoodBuilding.lineEquiv Good e hdim hgood L)
        (GoodBuilding.planeEquiv Good e hdim hgood P) (e.monotone h) := by
  rw [flagChain,apartmentChainEquiv,BipartitePathChains.chainEquiv_single]
  rfl

/-- Canonical two-line chains commute with actual subspace automorphisms. -/
theorem apartmentChainEquiv_line (L M : Line Good) :
    apartmentChainEquiv Good e hdim hgood (lineChain Good L M) =
      lineChain Good (GoodBuilding.lineEquiv Good e hdim hgood L)
        (GoodBuilding.lineEquiv Good e hdim hgood M) := by
  classical
  by_cases h : L = M
  · subst M
    rw [lineChain_self,lineChain_self,map_zero]
  · rw [lineChain_of_ne Good L M h,map_sub,apartmentChainEquiv_flag,
      apartmentChainEquiv_flag]
    exact (lineChain_of_common_plane Good _ _
      (GoodBuilding.planeEquiv Good e hdim hgood (spanPlane Good L M h))
      (e.monotone (line_le_spanPlane_left Good L M h))
      (e.monotone (line_le_spanPlane_right Good L M h))).symm

/-- The image of a literal apartment is the apartment of the three image lines. -/
theorem apartmentChainEquiv_apartment (L M N : Line Good) :
    apartmentChainEquiv Good e hdim hgood (apartmentChain Good L M N) =
      apartmentChain Good (GoodBuilding.lineEquiv Good e hdim hgood L)
        (GoodBuilding.lineEquiv Good e hdim hgood M)
        (GoodBuilding.lineEquiv Good e hdim hgood N) := by
  simp only [apartmentChain,map_add,apartmentChainEquiv_line]

/-- Restrict the genuine chain map to the actual incidence cycle kernel. -/
def apartmentCycleMap : Cycles Good →ₗ[ℚ] Cycles Good :=
  (((apartmentChainEquiv Good e hdim hgood).toLinearMap).comp
    (LinearMap.ker (boundary Good)).subtype).codRestrict _ (fun c =>
      BipartitePathChains.chainEquiv_mem_ker _ _ _ c.property)

theorem apartmentCycleMap_apartment (L M N : Line Good) :
    apartmentCycleMap Good e hdim hgood (apartmentCycle Good L M N) =
      apartmentCycle Good (GoodBuilding.lineEquiv Good e hdim hgood L)
        (GoodBuilding.lineEquiv Good e hdim hgood M)
        (GoodBuilding.lineEquiv Good e hdim hgood N) := by
  apply Subtype.ext
  exact apartmentChainEquiv_apartment Good e hdim hgood L M N

/-- Equivariance on apartments extends to the entire cycle kernel by genuine spanning. -/
theorem apartment_functional_equivariant (B : Line Good)
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    (F : Cycles Good →ₗ[ℚ] E) (T : E →ₗ[ℚ] E)
    (h : ∀ L M N,
      F (apartmentCycle Good (GoodBuilding.lineEquiv Good e hdim hgood L)
        (GoodBuilding.lineEquiv Good e hdim hgood M)
        (GoodBuilding.lineEquiv Good e hdim hgood N)) =
          T (F (apartmentCycle Good L M N))) :
    F.comp (apartmentCycleMap Good e hdim hgood) = T.comp F := by
  apply apartment_functional_ext Good B
  intro L M N
  simp only [LinearMap.comp_apply,apartmentCycleMap_apartment]
  exact h L M N

end TernaryPoly.GoodApartmentCycles
