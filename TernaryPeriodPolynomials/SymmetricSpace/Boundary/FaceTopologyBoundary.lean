module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyAtlas

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology

/-- Every line chart identifies the actual open stratum with strictly positive height. -/
theorem lineChart_positive (L : Line) (g : RationalGL) (hg : lineLabel g = L)
    (x : lineFace L) (hx : x ∈ (lineHalfSpaceChart L g hg).source) :
    0 < (lineHalfSpaceChart L g hg x).val 0 ↔ x.val ∈ openLineFace L := by
  have hr : x ∈ Set.range (lineParam L g hg) := by
    rw [lineParam_range]
    simpa only [lineHalfSpaceChart_source] using hx
  obtain ⟨p, rfl⟩ := hr
  rw [lineHalfSpaceChart_apply_param, faceHalfSpace_height, lineParam_positive]

theorem planeChart_positive (P : Plane) (g : RationalGL) (hg : planeLabel g = P)
    (x : planeFace P) (hx : x ∈ (planeHalfSpaceChart P g hg).source) :
    0 < (planeHalfSpaceChart P g hg x).val 0 ↔ x.val ∈ openPlaneFace P := by
  have hr : x ∈ Set.range (planeParam P g hg) := by
    rw [planeParam_range]
    simpa only [planeHalfSpaceChart_source] using hx
  obtain ⟨p, rfl⟩ := hr
  rw [planeHalfSpaceChart_apply_param, faceHalfSpace_height, planeParam_positive]

/-- The zero-height set of every line chart is exactly the incident full-flag boundary. -/
theorem lineChart_boundary (L : Line) (g : RationalGL) (hg : lineLabel g = L)
    (x : lineFace L) (hx : x ∈ (lineHalfSpaceChart L g hg).source) :
    (lineHalfSpaceChart L g hg x).val 0 = 0 ↔
      ∃ P, incidence L P ∧ x.val ∈ planeFace P := by
  have hr : x ∈ Set.range (lineParam L g hg) := by
    rw [lineParam_range]
    simpa only [lineHalfSpaceChart_source] using hx
  obtain ⟨p, rfl⟩ := hr
  rw [lineHalfSpaceChart_apply_param, faceHalfSpace_height, lineParam_boundary]

theorem planeChart_boundary (P : Plane) (g : RationalGL) (hg : planeLabel g = P)
    (x : planeFace P) (hx : x ∈ (planeHalfSpaceChart P g hg).source) :
    (planeHalfSpaceChart P g hg x).val 0 = 0 ↔
      ∃ L, incidence L P ∧ x.val ∈ lineFace L := by
  have hr : x ∈ Set.range (planeParam P g hg) := by
    rw [planeParam_range]
    simpa only [planeHalfSpaceChart_source] using hx
  obtain ⟨p, rfl⟩ := hr
  rw [planeHalfSpaceChart_apply_param, faceHalfSpace_height, planeParam_boundary]

/-- The chosen chart at every point has the same intrinsic open-stratum criterion. -/
theorem lineChartAt_positive (L : Line) (x : lineFace L) :
    0 < (chartAt (EuclideanHalfSpace 4) x x).val 0 ↔ x.val ∈ openLineFace L :=
  lineChart_positive L _ _ x (mem_chart_source _ x)

theorem planeChartAt_positive (P : Plane) (x : planeFace P) :
    0 < (chartAt (EuclideanHalfSpace 4) x x).val 0 ↔ x.val ∈ openPlaneFace P :=
  planeChart_positive P _ _ x (mem_chart_source _ x)

/-- Exact global boundary description for the actual four-dimensional closed line face. -/
theorem lineChartAt_boundary (L : Line) (x : lineFace L) :
    (chartAt (EuclideanHalfSpace 4) x x).val 0 = 0 ↔
      ∃ P, incidence L P ∧ x.val ∈ planeFace P :=
  lineChart_boundary L _ _ x (mem_chart_source _ x)

theorem planeChartAt_boundary (P : Plane) (x : planeFace P) :
    (chartAt (EuclideanHalfSpace 4) x x).val 0 = 0 ↔
      ∃ L, incidence L P ∧ x.val ∈ lineFace L :=
  planeChart_boundary P _ _ x (mem_chart_source _ x)

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
