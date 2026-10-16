module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyContractible
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyQuotientAtlas

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceBoundaryFaces

/-- The actual closed rational boundary faces and all nonempty full-flag intersections
are contractible. The whole-boundary nerve comparison remains a separate theorem. -/
theorem actual_boundary_face_contractibility :
    (∀ L : Line, ContractibleSpace (lineFace L)) ∧
    (∀ P : Plane, ContractibleSpace (planeFace P)) ∧
    (∀ L P, incidence L P → ContractibleSpace ↥(lineFace L ∩ planeFace P)) :=
  ⟨lineFace_contractible, planeFace_contractible, SymmetricSpaceBoundaryFaceModels.flagFace_contractible⟩

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
