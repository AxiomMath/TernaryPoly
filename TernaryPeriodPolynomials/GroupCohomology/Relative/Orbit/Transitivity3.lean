module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Corrections

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitTransitivity3
open ModThreeGoodAction RelativeOrbitCompletion RelativeOrbitResidues RelativeOrbitCorrections
open RelativeStabilizerCoordinates RelativeStabilizerConjugacy

/-- Every bad rational line lies in the actual row-e3 congruence orbit of the first coordinate line. -/
theorem bad_line (L : RationalSubspace) (hL : Module.finrank ℚ L = 1) (hbad : ¬Good3 L) :
    ∃ k : K3, act3 k L0 = L := by
  obtain ⟨g,hg⟩ := RationalLineBasis.rationalLine_eq_augmentedLine ⟨L,hL⟩
  have hL0 : mapSpace g L0 = L := (mapSpace_L0 g).trans (congrArg Subtype.val hg)
  have hrow : row g 0 = 0 := (bad3_L0_iff g).mp (hL0.symm ▸ hbad)
  have hk : g*lineCorrection (row g) ∈ K3 := by
    change row (g*lineCorrection (row g)) = ![0,0,1]
    rw [row_mul]
    exact line_row_correct (row g) hrow (row_ne_zero g)
  refine ⟨⟨g*lineCorrection (row g),hk⟩,?_⟩
  change mapSpace (g*lineCorrection (row g)) L0 = L
  rw [mapSpace_mul,show mapSpace (lineCorrection (row g)) L0 = L0 from line_stabilizes _,hL0]

/-- Every bad rational plane lies in the actual orbit of the first coordinate plane. -/
theorem bad_plane (P : RationalSubspace) (hP : Module.finrank ℚ P = 2) (hbad : ¬Good3 P) :
    ∃ k : K3, act3 k P0 = P := by
  obtain ⟨g,hg⟩ := plane_completion P hP
  have hr := (bad3_P0_iff g).mp (hg.symm ▸ hbad)
  have hk : g*planeCorrection (row g) ∈ K3 := by
    change row (g*planeCorrection (row g)) = ![0,0,1]
    rw [row_mul]
    exact plane_row_correct (row g) hr.1 hr.2 (row_ne_zero g)
  refine ⟨⟨g*planeCorrection (row g),hk⟩,?_⟩
  change mapSpace (g*planeCorrection (row g)) P0 = P
  rw [mapSpace_mul,show mapSpace (planeCorrection (row g)) P0 = P0 from plane_stabilizes_plane _,hg]

/-- Every bad-bad rational flag has a genuine congruence representative, obtained from an integral flag completion. -/
theorem bad_bad (L P : RationalSubspace) (hL : Module.finrank ℚ L = 1)
    (hP : Module.finrank ℚ P = 2) (hle : L ≤ P) (hbad : ¬Good3 P) :
    ∃ k : K3, act3 k L0 = L ∧ act3 k P0 = P := by
  obtain ⟨g,hgL,hgP⟩ := flag_completion L P hL hP hle
  have hr := (bad3_P0_iff g).mp (hgP.symm ▸ hbad)
  have hk : g*planeCorrection (row g) ∈ K3 := by
    change row (g*planeCorrection (row g)) = ![0,0,1]
    rw [row_mul]
    exact plane_row_correct (row g) hr.1 hr.2 (row_ne_zero g)
  refine ⟨⟨g*planeCorrection (row g),hk⟩,?_,?_⟩
  · change mapSpace (g*planeCorrection (row g)) L0 = L
    rw [mapSpace_mul,show mapSpace (planeCorrection (row g)) L0 = L0 from plane_stabilizes_line _,hgL]
  · change mapSpace (g*planeCorrection (row g)) P0 = P
    rw [mapSpace_mul,show mapSpace (planeCorrection (row g)) P0 = P0 from plane_stabilizes_plane _,hgP]

/-- Every bad-line/Good-plane rational flag has a genuine congruence representative. -/
theorem bad_good (L P : RationalSubspace) (hL : Module.finrank ℚ L = 1)
    (hP : Module.finrank ℚ P = 2) (hle : L ≤ P) (hbad : ¬Good3 L) (hgood : Good3 P) :
    ∃ k : K3, act3 k L0 = L ∧ act3 k P1 = P := by
  obtain ⟨g,hgL,hgP⟩ := flag_completion_P1 L P hL hP hle
  have hr0 := (bad3_L0_iff g).mp (hgL.symm ▸ hbad)
  have hr2 : row g 2 ≠ 0 := ((good3_P1_iff g).mp (hgP.symm ▸ hgood)).resolve_left (not_not.mpr hr0)
  have hk : g*bgCorrection (row g) ∈ K3 := by
    change row (g*bgCorrection (row g)) = ![0,0,1]
    rw [row_mul]
    exact bg_row_correct (row g) hr0 hr2
  refine ⟨⟨g*bgCorrection (row g),hk⟩,?_,?_⟩
  · change mapSpace (g*bgCorrection (row g)) L0 = L
    rw [mapSpace_mul,show mapSpace (bgCorrection (row g)) L0 = L0 from bg_stabilizes_line _,hgL]
  · change mapSpace (g*bgCorrection (row g)) P1 = P
    rw [mapSpace_mul,show mapSpace (bgCorrection (row g)) P1 = P1 from bg_stabilizes_plane _,hgP]

end TernaryPoly.RelativeOrbitTransitivity3
