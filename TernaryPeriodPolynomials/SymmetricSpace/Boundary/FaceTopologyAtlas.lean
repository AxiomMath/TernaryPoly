module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.SymmetricSpaceBoundaryFaceTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology

/-- Product half-space charts, also suitable for supported inward homotopies. -/
def lineProductChart (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    OpenPartialHomeomorph (lineFace L) ClosedFaceModel :=
  ((lineParam_isOpenEmbedding L g hg).toOpenPartialHomeomorph (lineParam L g hg)).symm

def planeProductChart (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    OpenPartialHomeomorph (planeFace P) ClosedFaceModel :=
  ((planeParam_isOpenEmbedding P g hg).toOpenPartialHomeomorph (planeParam P g hg)).symm

@[simp] theorem lineProductChart_source (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    (lineProductChart L g hg).source = Subtype.val ⁻¹' Set.range (chart g) := by
  simp [lineProductChart, lineParam_range]

@[simp] theorem planeProductChart_source (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    (planeProductChart P g hg).source = Subtype.val ⁻¹' Set.range (chart g) := by
  simp [planeProductChart, planeParam_range]

@[simp] theorem lineProductChart_target (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    (lineProductChart L g hg).target = Set.univ := by simp [lineProductChart]

@[simp] theorem planeProductChart_target (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    (planeProductChart P g hg).target = Set.univ := by simp [planeProductChart]

@[simp] theorem lineProductChart_apply_param (L : Line) (g : RationalGL)
    (hg : lineLabel g = L) (p : ClosedFaceModel) :
    lineProductChart L g hg (lineParam L g hg p) = p :=
  (lineParam_isOpenEmbedding L g hg).toOpenPartialHomeomorph_left_inv _

@[simp] theorem planeProductChart_apply_param (P : Plane) (g : RationalGL)
    (hg : planeLabel g = P) (p : ClosedFaceModel) :
    planeProductChart P g hg (planeParam P g hg p) = p :=
  (planeParam_isOpenEmbedding P g hg).toOpenPartialHomeomorph_left_inv _

def lineHalfSpaceParam (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    EuclideanHalfSpace 4 → lineFace L := lineParam L g hg ∘ faceHalfSpaceHomeomorph.symm

def planeHalfSpaceParam (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    EuclideanHalfSpace 4 → planeFace P := planeParam P g hg ∘ faceHalfSpaceHomeomorph.symm

theorem lineHalfSpaceParam_isOpenEmbedding (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    IsOpenEmbedding (lineHalfSpaceParam L g hg) :=
  (lineParam_isOpenEmbedding L g hg).comp faceHalfSpaceHomeomorph.symm.isOpenEmbedding

theorem planeHalfSpaceParam_isOpenEmbedding (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    IsOpenEmbedding (planeHalfSpaceParam P g hg) :=
  (planeParam_isOpenEmbedding P g hg).comp faceHalfSpaceHomeomorph.symm.isOpenEmbedding

@[simp] theorem lineHalfSpaceParam_range (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    Set.range (lineHalfSpaceParam L g hg) = Subtype.val ⁻¹' Set.range (chart g) := by
  rw [lineHalfSpaceParam, faceHalfSpaceHomeomorph.symm.surjective.range_comp, lineParam_range]

@[simp] theorem planeHalfSpaceParam_range (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    Set.range (planeHalfSpaceParam P g hg) = Subtype.val ⁻¹' Set.range (chart g) := by
  rw [planeHalfSpaceParam, faceHalfSpaceHomeomorph.symm.surjective.range_comp, planeParam_range]

/-- Genuine four-dimensional half-space charts on the entire closed line face. -/
def lineHalfSpaceChart (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    OpenPartialHomeomorph (lineFace L) (EuclideanHalfSpace 4) :=
  ((lineHalfSpaceParam_isOpenEmbedding L g hg).toOpenPartialHomeomorph
    (lineHalfSpaceParam L g hg)).symm

def planeHalfSpaceChart (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    OpenPartialHomeomorph (planeFace P) (EuclideanHalfSpace 4) :=
  ((planeHalfSpaceParam_isOpenEmbedding P g hg).toOpenPartialHomeomorph
    (planeHalfSpaceParam P g hg)).symm

@[simp] theorem lineHalfSpaceChart_source (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    (lineHalfSpaceChart L g hg).source = Subtype.val ⁻¹' Set.range (chart g) := by
  simp [lineHalfSpaceChart]

@[simp] theorem planeHalfSpaceChart_source (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    (planeHalfSpaceChart P g hg).source = Subtype.val ⁻¹' Set.range (chart g) := by
  simp [planeHalfSpaceChart]

@[simp] theorem lineHalfSpaceChart_target (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    (lineHalfSpaceChart L g hg).target = Set.univ := by simp [lineHalfSpaceChart]

@[simp] theorem planeHalfSpaceChart_target (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    (planeHalfSpaceChart P g hg).target = Set.univ := by simp [planeHalfSpaceChart]

@[simp] theorem lineHalfSpaceChart_apply_param (L : Line) (g : RationalGL)
    (hg : lineLabel g = L) (p : ClosedFaceModel) :
    lineHalfSpaceChart L g hg (lineParam L g hg p) = faceHalfSpaceHomeomorph p := by
  have h := (lineHalfSpaceParam_isOpenEmbedding L g hg).toOpenPartialHomeomorph_left_inv
    (lineHalfSpaceParam L g hg) (x := faceHalfSpaceHomeomorph p)
  simpa only [lineHalfSpaceChart, lineHalfSpaceParam, Function.comp_apply,
    Homeomorph.symm_apply_apply] using h

@[simp] theorem planeHalfSpaceChart_apply_param (P : Plane) (g : RationalGL)
    (hg : planeLabel g = P) (p : ClosedFaceModel) :
    planeHalfSpaceChart P g hg (planeParam P g hg p) = faceHalfSpaceHomeomorph p := by
  have h := (planeHalfSpaceParam_isOpenEmbedding P g hg).toOpenPartialHomeomorph_left_inv
    (planeHalfSpaceParam P g hg) (x := faceHalfSpaceHomeomorph p)
  simpa only [planeHalfSpaceChart, planeHalfSpaceParam, Function.comp_apply,
    Homeomorph.symm_apply_apply] using h

/-- Select actual rational-coordinate witnesses for points of the entire closed face. -/
def lineFrame (L : Line) (x : lineFace L) : RationalGL := x.property.choose
def linePoint (L : Line) (x : lineFace L) : Corner := x.property.choose_spec.choose

theorem lineFrame_spec (L : Line) (x : lineFace L) :
    (linePoint L x).2.1.val = 0 ∧ lineLabel (lineFrame L x) = L ∧
      chart (lineFrame L x) (linePoint L x) = x.val := x.property.choose_spec.choose_spec

def planeFrame (P : Plane) (x : planeFace P) : RationalGL := x.property.choose
def planePoint (P : Plane) (x : planeFace P) : Corner := x.property.choose_spec.choose

theorem planeFrame_spec (P : Plane) (x : planeFace P) :
    (planePoint P x).2.2.val = 0 ∧ planeLabel (planeFrame P x) = P ∧
      chart (planeFrame P x) (planePoint P x) = x.val := x.property.choose_spec.choose_spec

/-- The given subspace topology carries this four-dimensional half-space atlas. -/
instance lineFace_chartedSpace (L : Line) : ChartedSpace (EuclideanHalfSpace 4) (lineFace L) where
  atlas := {e | ∃ g hg, e = lineHalfSpaceChart L g hg}
  chartAt x := lineHalfSpaceChart L (lineFrame L x) (lineFrame_spec L x).2.1
  mem_chart_source x := by
    rw [lineHalfSpaceChart_source]
    exact ⟨linePoint L x, (lineFrame_spec L x).2.2⟩
  chart_mem_atlas x := ⟨lineFrame L x, (lineFrame_spec L x).2.1, rfl⟩

instance planeFace_chartedSpace (P : Plane) : ChartedSpace (EuclideanHalfSpace 4) (planeFace P) where
  atlas := {e | ∃ g hg, e = planeHalfSpaceChart P g hg}
  chartAt x := planeHalfSpaceChart P (planeFrame P x) (planeFrame_spec P x).2.1
  mem_chart_source x := by
    rw [planeHalfSpaceChart_source]
    exact ⟨planePoint P x, (planeFrame_spec P x).2.2⟩
  chart_mem_atlas x := ⟨planeFrame P x, (planeFrame_spec P x).2.1, rfl⟩

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
