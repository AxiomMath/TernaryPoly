module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyDescent

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology
open IntegralGL3Congruence

/-- Standard four-dimensional half-space charts on the true compact quotient. -/
def lineOrbitHalfSpaceChart (L : Line) (x : lineFace L) :
    OpenPartialHomeomorph (LineFaceOrbit L) (EuclideanHalfSpace 4) :=
  (lineOrbitChart L x).trans faceHalfSpaceHomeomorph.toOpenPartialHomeomorph

def planeOrbitHalfSpaceChart (P : Plane) (x : planeFace P) :
    OpenPartialHomeomorph (PlaneFaceOrbit P) (EuclideanHalfSpace 4) :=
  (planeOrbitChart P x).trans faceHalfSpaceHomeomorph.toOpenPartialHomeomorph

@[simp] theorem lineOrbitHalfSpaceChart_source (L : Line) (x : lineFace L) :
    (lineOrbitHalfSpaceChart L x).source = (lineOrbitChart L x).source := by
  simp [lineOrbitHalfSpaceChart]

@[simp] theorem planeOrbitHalfSpaceChart_source (P : Plane) (x : planeFace P) :
    (planeOrbitHalfSpaceChart P x).source = (planeOrbitChart P x).source := by
  simp [planeOrbitHalfSpaceChart]

def lineOrbitRepresentative (L : Line) (q : LineFaceOrbit L) : lineFace L :=
  (Quotient.mk_surjective q).choose

def planeOrbitRepresentative (P : Plane) (q : PlaneFaceOrbit P) : planeFace P :=
  (Quotient.mk_surjective q).choose

theorem lineOrbitRepresentative_spec (L : Line) (q : LineFaceOrbit L) :
    RestrictedQuotient.faceProjection (lineFace L) (lineOrbitRepresentative L q) = q :=
  (Quotient.mk_surjective q).choose_spec

theorem planeOrbitRepresentative_spec (P : Plane) (q : PlaneFaceOrbit P) :
    RestrictedQuotient.faceProjection (planeFace P) (planeOrbitRepresentative P q) = q :=
  (Quotient.mk_surjective q).choose_spec

instance lineFaceOrbit_chartedSpace (L : Line) : ChartedSpace (EuclideanHalfSpace 4) (LineFaceOrbit L) where
  atlas := Set.range (lineOrbitHalfSpaceChart L)
  chartAt q := lineOrbitHalfSpaceChart L (lineOrbitRepresentative L q)
  mem_chart_source q := by
    rw [lineOrbitHalfSpaceChart_source]
    simpa only [lineOrbitRepresentative_spec] using
      lineOrbitChart_mem L (lineOrbitRepresentative L q)
  chart_mem_atlas q := ⟨lineOrbitRepresentative L q, rfl⟩

instance planeFaceOrbit_chartedSpace (P : Plane) : ChartedSpace (EuclideanHalfSpace 4) (PlaneFaceOrbit P) where
  atlas := Set.range (planeOrbitHalfSpaceChart P)
  chartAt q := planeOrbitHalfSpaceChart P (planeOrbitRepresentative P q)
  mem_chart_source q := by
    rw [planeOrbitHalfSpaceChart_source]
    simpa only [planeOrbitRepresentative_spec] using
      planeOrbitChart_mem P (planeOrbitRepresentative P q)
  chart_mem_atlas q := ⟨planeOrbitRepresentative P q, rfl⟩

/-- The quotient manifold's intrinsic interior is exactly the actual open-face quotient. -/
theorem lineOrbitChartAt_positive (L : Line) (q : LineFaceOrbit L) :
    0 < (chartAt (EuclideanHalfSpace 4) q q).val 0 ↔ q ∈ lineOrbitInterior L := by
  change 0 < (lineOrbitChart L (lineOrbitRepresentative L q) q).2.val ↔ _
  apply (lineOrbitChart_positive L _ q _).symm
  have h := mem_chart_source (EuclideanHalfSpace 4) q
  simpa only [chartAt, ChartedSpace.chartAt, lineOrbitHalfSpaceChart_source] using h

theorem planeOrbitChartAt_positive (P : Plane) (q : PlaneFaceOrbit P) :
    0 < (chartAt (EuclideanHalfSpace 4) q q).val 0 ↔ q ∈ planeOrbitInterior P := by
  change 0 < (planeOrbitChart P (planeOrbitRepresentative P q) q).2.val ↔ _
  apply (planeOrbitChart_positive P _ q _).symm
  have h := mem_chart_source (EuclideanHalfSpace 4) q
  simpa only [chartAt, ChartedSpace.chartAt, planeOrbitHalfSpaceChart_source] using h

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
