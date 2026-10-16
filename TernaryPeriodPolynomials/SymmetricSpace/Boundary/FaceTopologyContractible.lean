module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyDescent
public import TernaryPeriodPolynomials.Analysis.Finite.InwardHomotopy
public import TernaryPeriodPolynomials.Topology.InwardHomotopyCovering

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology
open IntegralGL3Congruence

/-- Compactness of the true face quotient makes finitely many supported pushes sufficient. -/
theorem lineOrbit_exists_globalInward (L : Line) :
    ∃ H : InwardHomotopy.LocalDeformation (lineOrbitInterior L),
      ∀ q, H.homotopy (1, q) ∈ lineOrbitInterior L :=
  InwardHomotopy.exists_global (lineOrbitInterior_open L) (lineOrbit_localInward L)

theorem planeOrbit_exists_globalInward (P : Plane) :
    ∃ H : InwardHomotopy.LocalDeformation (planeOrbitInterior P),
      ∀ q, H.homotopy (1, q) ∈ planeOrbitInterior P :=
  InwardHomotopy.exists_global (planeOrbitInterior_open P) (planeOrbit_localInward P)

def lineOrbitInward (L : Line) : InwardHomotopy.LocalDeformation (lineOrbitInterior L) :=
  (lineOrbit_exists_globalInward L).choose

def planeOrbitInward (P : Plane) : InwardHomotopy.LocalDeformation (planeOrbitInterior P) :=
  (planeOrbit_exists_globalInward P).choose

theorem lineOrbitInward_endpoint (L : Line) (q : LineFaceOrbit L) :
    (lineOrbitInward L).homotopy (1, q) ∈ lineOrbitInterior L :=
  (lineOrbit_exists_globalInward L).choose_spec q

theorem planeOrbitInward_endpoint (P : Plane) (q : PlaneFaceOrbit P) :
    (planeOrbitInward P).homotopy (1, q) ∈ planeOrbitInterior P :=
  (planeOrbit_exists_globalInward P).choose_spec q

/-- Identify the preimage of the quotient interior with the actual open line stratum. -/
def linePreimageInteriorHomeomorph (L : Line) :
    (RestrictedQuotient.faceProjection (lineFace L) ⁻¹' lineOrbitInterior L) ≃ₜ openLineFace L :=
  (Homeomorph.setCongr (lineOrbitInterior_preimage L)).trans (lineFaceInteriorHomeomorph L)

def planePreimageInteriorHomeomorph (P : Plane) :
    (RestrictedQuotient.faceProjection (planeFace P) ⁻¹' planeOrbitInterior P) ≃ₜ openPlaneFace P :=
  (Homeomorph.setCongr (planeOrbitInterior_preimage P)).trans (planeFaceInteriorHomeomorph P)

/-- The literal inclusion of the open line stratum is a homotopy equivalence, constructed
by lifting the actual global inward homotopy through the true face covering. -/
def lineOpenInclusionHomotopyEquiv (L : Line) :
    ContinuousMap.HomotopyEquiv (openLineFace L) (lineFace L) :=
  (linePreimageInteriorHomeomorph L).symm.toHomotopyEquiv.trans
    (InwardHomotopyCovering.liftedHomotopyEquiv (lineFace_covering L)
      (lineOrbitInward L).homotopy (lineOrbitInward L).zero
      (lineOrbitInward L).preserves (lineOrbitInward_endpoint L))

def planeOpenInclusionHomotopyEquiv (P : Plane) :
    ContinuousMap.HomotopyEquiv (openPlaneFace P) (planeFace P) :=
  (planePreimageInteriorHomeomorph P).symm.toHomotopyEquiv.trans
    (InwardHomotopyCovering.liftedHomotopyEquiv (planeFace_covering P)
      (planeOrbitInward P).homotopy (planeOrbitInward P).zero
      (planeOrbitInward P).preserves (planeOrbitInward_endpoint P))

@[simp] theorem lineOpenInclusionHomotopyEquiv_apply (L : Line) (x : openLineFace L) :
    (lineOpenInclusionHomotopyEquiv L x).val = x.val := rfl

@[simp] theorem planeOpenInclusionHomotopyEquiv_apply (P : Plane) (x : openPlaneFace P) :
    (planeOpenInclusionHomotopyEquiv P x).val = x.val := rfl

/-- Entire actual closed line faces are contractible through the proved quotient/inward/lift bridge. -/
instance lineFace_contractible (L : Line) : ContractibleSpace (lineFace L) :=
  (lineOpenInclusionHomotopyEquiv L).symm.contractibleSpace

/-- Entire actual closed plane faces are contractible through the same genuine geometric bridge. -/
instance planeFace_contractible (P : Plane) : ContractibleSpace (planeFace P) :=
  (planeOpenInclusionHomotopyEquiv P).symm.contractibleSpace

/-- Both types of actual closed rational boundary face are contractible, without extra hypotheses. -/
theorem actual_closed_faces_contractible :
    (∀ L : Line, ContractibleSpace (lineFace L)) ∧
    (∀ P : Plane, ContractibleSpace (planeFace P)) :=
  ⟨lineFace_contractible, planeFace_contractible⟩

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
