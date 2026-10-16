module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyInward
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyFamilies

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology
open IntegralGL3Congruence SymmetricSpaceBordifiedQuotient

/-- Consumer-facing global models: open strata and all nonempty corners are contractible. -/
theorem actual_open_faces_and_corners_contractible :
    (∀ L : Line, ContractibleSpace (openLineFace L)) ∧
    (∀ P : Plane, ContractibleSpace (openPlaneFace P)) ∧
    (∀ L P, incidence L P → ContractibleSpace ↥(lineFace L ∩ planeFace P)) :=
  ⟨fun _ => inferInstance, fun _ => inferInstance, flagFace_contractible⟩

/-- The atlas boundary is precisely the intrinsic incident-flag boundary on both face types. -/
theorem actual_closed_face_boundary :
    (∀ (L : Line) (x : lineFace L),
      (chartAt (EuclideanHalfSpace 4) x x).val 0 = 0 ↔
        ∃ P, incidence L P ∧ x.val ∈ planeFace P) ∧
    (∀ (P : Plane) (x : planeFace P),
      (chartAt (EuclideanHalfSpace 4) x x).val 0 = 0 ↔
        ∃ L, incidence L P ∧ x.val ∈ lineFace L) :=
  ⟨lineChartAt_boundary, planeChartAt_boundary⟩

/-- Actual compact images in the arithmetic bordification, without silently identifying
these images with a face-stabilizer quotient. -/
theorem actual_closed_face_images_compact :
    (∀ L, IsCompact (projection principalSix '' lineFace L)) ∧
    (∀ P, IsCompact (projection principalSix '' planeFace P)) :=
  ⟨projection_lineFace_compact, projection_planeFace_compact⟩

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
