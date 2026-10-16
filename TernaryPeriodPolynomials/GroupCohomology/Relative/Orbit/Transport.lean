module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Transitivity3
public import TernaryPeriodPolynomials.GroupCohomology.Relative.PermutationIndices
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitTransport
open ModThreeGoodAction RelativeOrbitCompletion RelativeStabilizerCoordinates RelativeStabilizerConjugacy
open RelativePermutationIndices

/-- Pull a rational subspace back through the fixed integral change of covector. -/
def unchange (L : RationalSubspace) : RationalSubspace := mapSpace B⁻¹ L

theorem change_unchange (L : RationalSubspace) : changeSpace (unchange L) = L := by
  change mapSpace B (mapSpace B⁻¹ L) = L
  rw [← mapSpace_mul,mul_inv_cancel,mapSpace_one]
theorem unchange_finrank (L : RationalSubspace) :
    Module.finrank ℚ (unchange L) = Module.finrank ℚ L := mapSpace_finrank _ _
theorem good_unchange (L : RationalSubspace) : Good3 (unchange L) ↔ Good L := by
  rw [← good_changeSpace_iff,change_unchange]
theorem change_finrank (L : RationalSubspace) :
    Module.finrank ℚ (changeSpace L) = Module.finrank ℚ L := mapSpace_finrank _ _

/-- The specified standard bad-line representative in the original covector coordinates. -/
def baseLine : BadLine :=
  ⟨⟨changeSpace L0,(change_finrank L0).trans finrank_L0,trivial⟩,
    fun h => not_good3_L0 ((good_changeSpace_iff L0).mp h)⟩
/-- The specified standard bad-plane representative in the original coordinates. -/
def basePlane : BadPlane :=
  ⟨⟨changeSpace P0,(change_finrank P0).trans finrank_P0,
    ⟨baseLine.val,Submodule.map_mono L0_le_P0⟩⟩,
    fun h => not_good3_P0 ((good_changeSpace_iff P0).mp h)⟩

def baseGoodPlane : OrdinaryIncidence.Plane :=
  ⟨changeSpace P1,(change_finrank P1).trans finrank_P1,
    ⟨baseLine.val,Submodule.map_mono L0_le_P1⟩⟩

def baseBB : BB :=
  ⟨⟨(baseLine.val,basePlane.val),GoodIncidenceConnected.line_lt_plane (fun _ => True)
    (Submodule.map_mono L0_le_P0)⟩,baseLine.property,basePlane.property⟩
def baseBG : BG :=
  ⟨⟨(baseLine.val,baseGoodPlane),GoodIncidenceConnected.line_lt_plane (fun _ => True)
    (Submodule.map_mono L0_le_P1)⟩,baseLine.property,(good_changeSpace_iff P1).mpr good3_P1⟩

/-- Exhaustive bad-line orbit for the actual original K action. -/
theorem badLine_transitive (L : BadLine) : ∃ k : K, badLineAction k baseLine = L := by
  obtain ⟨k,hk⟩ := RelativeOrbitTransitivity3.bad_line (unchange L.val.val)
    ((unchange_finrank _).trans L.val.property.1) (fun h => L.property ((good_unchange _).mp h))
  refine ⟨K3EquivK k,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change act (K3EquivK k) (changeSpace L0) = L.val.val
  rw [← changeSpace_act3,hk,change_unchange]

/-- Exhaustive bad-plane orbit for the actual original K action. -/
theorem badPlane_transitive (P : BadPlane) : ∃ k : K, badPlaneAction k basePlane = P := by
  obtain ⟨k,hk⟩ := RelativeOrbitTransitivity3.bad_plane (unchange P.val.val)
    ((unchange_finrank _).trans P.val.property.1) (fun h => P.property ((good_unchange _).mp h))
  refine ⟨K3EquivK k,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change act (K3EquivK k) (changeSpace P0) = P.val.val
  rw [← changeSpace_act3,hk,change_unchange]

/-- Exhaustive bad-bad flag orbit, with its actual oriented incidence pair retained. -/
theorem bb_transitive (e : BB) : ∃ k : K, bbAction k baseBB = e := by
  obtain ⟨k,hL,hP⟩ := RelativeOrbitTransitivity3.bad_bad
    (unchange e.val.val.1.val) (unchange e.val.val.2.val)
    ((unchange_finrank _).trans e.val.val.1.property.1)
    ((unchange_finrank _).trans e.val.val.2.property.1)
    (Submodule.map_mono e.val.property.le) (fun h => e.property.2 ((good_unchange _).mp h))
  refine ⟨K3EquivK k,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change act (K3EquivK k) (changeSpace L0) = e.val.val.1.val
    rw [← changeSpace_act3,hL,change_unchange]
  · apply Subtype.ext
    change act (K3EquivK k) (changeSpace P0) = e.val.val.2.val
    rw [← changeSpace_act3,hP,change_unchange]

/-- Exhaustive bad-Good flag orbit for the same orientation-preserving action. -/
theorem bg_transitive (e : BG) : ∃ k : K, bgAction k baseBG = e := by
  obtain ⟨k,hL,hP⟩ := RelativeOrbitTransitivity3.bad_good
    (unchange e.val.val.1.val) (unchange e.val.val.2.val)
    ((unchange_finrank _).trans e.val.val.1.property.1)
    ((unchange_finrank _).trans e.val.val.2.property.1)
    (Submodule.map_mono e.val.property.le) (fun h => e.property.1 ((good_unchange _).mp h))
    ((good_unchange _).mpr e.property.2)
  refine ⟨K3EquivK k,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change act (K3EquivK k) (changeSpace L0) = e.val.val.1.val
    rw [← changeSpace_act3,hL,change_unchange]
  · apply Subtype.ext
    change act (K3EquivK k) (changeSpace P1) = e.val.val.2.val
    rw [← changeSpace_act3,hP,change_unchange]

end TernaryPoly.RelativeOrbitTransport
