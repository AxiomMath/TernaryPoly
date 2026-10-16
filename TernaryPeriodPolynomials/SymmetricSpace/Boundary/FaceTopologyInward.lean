module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyBoundary
public import TernaryPeriodPolynomials.SymmetricSpace.Corner.Separation
public import TernaryPeriodPolynomials.Topology.Supported.InwardManifold

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology

/-- The product chart's positive-height locus is literally the open line stratum. -/
theorem lineProductChart_positive (L : Line) (g : RationalGL) (hg : lineLabel g = L)
    (x : lineFace L) (hx : x ∈ (lineProductChart L g hg).source) :
    x.val ∈ openLineFace L ↔ 0 < (lineProductChart L g hg x).2.val := by
  have hr : x ∈ Set.range (lineParam L g hg) := by
    rw [lineParam_range]
    simpa only [lineProductChart_source] using hx
  obtain ⟨p, rfl⟩ := hr
  rw [lineProductChart_apply_param, lineParam_positive]

theorem planeProductChart_positive (P : Plane) (g : RationalGL) (hg : planeLabel g = P)
    (x : planeFace P) (hx : x ∈ (planeProductChart P g hg).source) :
    x.val ∈ openPlaneFace P ↔ 0 < (planeProductChart P g hg x).2.val := by
  have hr : x ∈ Set.range (planeParam P g hg) := by
    rw [planeParam_range]
    simpa only [planeProductChart_source] using hx
  obtain ⟨p, rfl⟩ := hr
  rw [planeProductChart_apply_param, planeParam_positive]

/-- Every point of the entire closed line face admits a supported inward deformation.
This local result alone is not a contraction of the noncompact closed face. -/
theorem lineFace_localInward (L : Line) (x : lineFace L) :
    ∃ H : InwardHomotopy.LocalDeformation (Subtype.val ⁻¹' openLineFace L : Set (lineFace L)),
      H.homotopy (1, x) ∈ (Subtype.val ⁻¹' openLineFace L : Set (lineFace L)) := by
  let g := lineFrame L x
  have hg : lineLabel g = L := (lineFrame_spec L x).2.1
  apply SupportedInward.exists_localDeformation
    (Subtype.val ⁻¹' openLineFace L) (lineProductChart L g hg)
    (fun y hy => lineProductChart_positive L g hg y hy) x
  rw [lineProductChart_source]
  exact ⟨linePoint L x, (lineFrame_spec L x).2.2⟩

theorem planeFace_localInward (P : Plane) (x : planeFace P) :
    ∃ H : InwardHomotopy.LocalDeformation (Subtype.val ⁻¹' openPlaneFace P : Set (planeFace P)),
      H.homotopy (1, x) ∈ (Subtype.val ⁻¹' openPlaneFace P : Set (planeFace P)) := by
  let g := planeFrame P x
  have hg : planeLabel g = P := (planeFrame_spec P x).2.1
  apply SupportedInward.exists_localDeformation
    (Subtype.val ⁻¹' openPlaneFace P) (planeProductChart P g hg)
    (fun y hy => planeProductChart_positive P g hg y hy) x
  rw [planeProductChart_source]
  exact ⟨planePoint P x, (planeFrame_spec P x).2.2⟩

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
