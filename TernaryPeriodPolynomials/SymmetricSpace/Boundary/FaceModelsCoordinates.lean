module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceModels

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceModels
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces Topology

abbrev PositiveRoot := Set.Ioi (0 : ℝ)
abbrev OpenFaceModel := Vec3 × PositiveRoot
abbrev ClosedFaceModel := Vec3 × HalfLine

def zeroRoot : HalfLine := ⟨0, by norm_num [HalfLine]⟩

def lineCoordinates : OpenFaceModel ≃ₜ lineLocus where
  toFun p := ⟨(p.1, zeroRoot, ⟨p.2.val, (show (0 : ℝ) < p.2.val from p.2.property).le⟩), rfl, p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2.2.val, p.property.2⟩)
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext ?_ rfl
    exact Subtype.ext p.property.1.symm
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def planeCoordinates : OpenFaceModel ≃ₜ planeLocus where
  toFun p := ⟨(p.1, ⟨p.2.val, (show (0 : ℝ) < p.2.val from p.2.property).le⟩, zeroRoot), p.2.property, rfl⟩
  invFun p := (p.val.1, ⟨p.val.2.1.val, p.property.1⟩)
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    exact Subtype.ext p.property.2.symm
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def cornerCoordinates : Vec3 ≃ₜ cornerLocus where
  toFun u := ⟨(u, zeroRoot, zeroRoot), rfl, rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact Prod.ext (Subtype.ext p.property.1.symm) (Subtype.ext p.property.2.symm)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Explicit unipotent/root parametrization of the whole actual open line face. -/
def openLineHomeomorph (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    OpenFaceModel ≃ₜ openLineFace L := lineCoordinates.trans (lineLocusHomeomorph L g hg)

/-- Explicit unipotent/root parametrization of the whole actual open plane face. -/
def openPlaneHomeomorph (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    OpenFaceModel ≃ₜ openPlaneFace P := planeCoordinates.trans (planeLocusHomeomorph P g hg)

/-- The entire actual full-flag intersection is a single copy of three-dimensional real space. -/
def flagHomeomorph (L : Line) (P : Plane) (g : RationalGL)
    (hL : lineLabel g = L) (hP : planeLabel g = P) :
    Vec3 ≃ₜ ↥(lineFace L ∩ planeFace P) :=
  cornerCoordinates.trans (cornerLocusHomeomorph L P g hL hP)

@[simp] theorem openLineHomeomorph_val (L : Line) (g : RationalGL)
    (hg : lineLabel g = L) (p : OpenFaceModel) :
    (openLineHomeomorph L g hg p).val =
      chart g (p.1, zeroRoot, ⟨p.2.val, (show (0 : ℝ) < p.2.val from p.2.property).le⟩) := rfl

@[simp] theorem openPlaneHomeomorph_val (P : Plane) (g : RationalGL)
    (hg : planeLabel g = P) (p : OpenFaceModel) :
    (openPlaneHomeomorph P g hg p).val =
      chart g (p.1, ⟨p.2.val, (show (0 : ℝ) < p.2.val from p.2.property).le⟩, zeroRoot) := rfl

@[simp] theorem flagHomeomorph_val (L : Line) (P : Plane) (g : RationalGL)
    (hL : lineLabel g = L) (hP : planeLabel g = P) (u : Vec3) :
    (flagHomeomorph L P g hL hP u).val = chart g (u, zeroRoot, zeroRoot) := rfl

instance positiveRoot_contractible : ContractibleSpace PositiveRoot :=
  (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩

instance openLineFace_contractible (L : Line) : ContractibleSpace (openLineFace L) := by
  obtain ⟨_, g, p, hz, hg, he⟩ := lineFace_nonempty L
  exact (openLineHomeomorph L g hg).symm.contractibleSpace

instance openPlaneFace_contractible (P : Plane) : ContractibleSpace (openPlaneFace P) := by
  obtain ⟨_, g, p, hz, hg, he⟩ := planeFace_nonempty P
  exact (openPlaneHomeomorph P g hg).symm.contractibleSpace

theorem flagFace_contractible (L : Line) (P : Plane) (h : incidence L P) :
    ContractibleSpace ↥(lineFace L ∩ planeFace P) := by
  obtain ⟨g, hL, hP⟩ := exists_frame_for_incident L P h
  exact (flagHomeomorph L P g hL hP).symm.contractibleSpace

end TernaryPoly.SymmetricSpaceBoundaryFaceModels
