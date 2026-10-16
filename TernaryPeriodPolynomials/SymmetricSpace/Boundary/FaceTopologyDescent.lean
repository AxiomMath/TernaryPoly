module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyQuotientInterior

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology
open IntegralGL3Congruence

section General
variable {Y Z W : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  {p : Y → Z}

/-- Descend an actual local chart by a genuine local inverse of the covering map. -/
def descendedChart (hp : IsCoveringMap p) (y : Y) (c : OpenPartialHomeomorph Y W) :
    OpenPartialHomeomorph Z W := (hp.isLocalHomeomorph.localInverseAt y).trans c

theorem descendedChart_mem (hp : IsCoveringMap p) (y : Y) (c : OpenPartialHomeomorph Y W)
    (hy : y ∈ c.source) : p y ∈ (descendedChart hp y c).source := by
  refine ⟨hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source, ?_⟩
  change hp.isLocalHomeomorph.localInverseAt y (p y) ∈ c.source
  simpa only [hp.isLocalHomeomorph.localInverseAt_apply_self] using hy

/-- Positivity descends precisely when the upstairs interior is the actual preimage. -/
theorem descendedChart_positive (hp : IsCoveringMap p) (y : Y)
    (c : OpenPartialHomeomorph Y ClosedFaceModel) (U : Set Z)
    (hU : ∀ z ∈ c.source, z ∈ p ⁻¹' U ↔ 0 < (c z).2.val)
    (z : Z) (hz : z ∈ (descendedChart hp y c).source) :
    z ∈ U ↔ 0 < (descendedChart hp y c z).2.val := by
  have he : p (hp.isLocalHomeomorph.localInverseAt y z) = z := by
    have h := (hp.isLocalHomeomorph.localInverseAt y).left_inv hz.1
    simpa only [hp.isLocalHomeomorph.localInverseAt_symm] using h
  change z ∈ U ↔ 0 < (c (hp.isLocalHomeomorph.localInverseAt y z)).2.val
  have hh := hU (hp.isLocalHomeomorph.localInverseAt y z) hz.2
  change p (hp.isLocalHomeomorph.localInverseAt y z) ∈ U ↔ _ at hh
  rwa [he] at hh

end General

/-- A true quotient chart on the compact actual line-face stabilizer quotient. -/
def lineOrbitChart (L : Line) (x : lineFace L) :
    OpenPartialHomeomorph (LineFaceOrbit L) ClosedFaceModel :=
  descendedChart (lineFace_covering L) x
    (lineProductChart L (lineFrame L x) (lineFrame_spec L x).2.1)

def planeOrbitChart (P : Plane) (x : planeFace P) :
    OpenPartialHomeomorph (PlaneFaceOrbit P) ClosedFaceModel :=
  descendedChart (planeFace_covering P) x
    (planeProductChart P (planeFrame P x) (planeFrame_spec P x).2.1)

theorem lineOrbitChart_mem (L : Line) (x : lineFace L) :
    RestrictedQuotient.faceProjection (lineFace L) x ∈ (lineOrbitChart L x).source := by
  apply descendedChart_mem
  rw [lineProductChart_source]
  exact ⟨linePoint L x, (lineFrame_spec L x).2.2⟩

theorem planeOrbitChart_mem (P : Plane) (x : planeFace P) :
    RestrictedQuotient.faceProjection (planeFace P) x ∈ (planeOrbitChart P x).source := by
  apply descendedChart_mem
  rw [planeProductChart_source]
  exact ⟨planePoint P x, (planeFrame_spec P x).2.2⟩

theorem lineOrbitChart_positive (L : Line) (x : lineFace L) (q : LineFaceOrbit L)
    (hq : q ∈ (lineOrbitChart L x).source) :
    q ∈ lineOrbitInterior L ↔ 0 < (lineOrbitChart L x q).2.val := by
  apply descendedChart_positive (lineFace_covering L) x _ (lineOrbitInterior L) _ q hq
  intro y hy
  rw [lineOrbitInterior_preimage]
  exact lineProductChart_positive L _ _ y hy

theorem planeOrbitChart_positive (P : Plane) (x : planeFace P) (q : PlaneFaceOrbit P)
    (hq : q ∈ (planeOrbitChart P x).source) :
    q ∈ planeOrbitInterior P ↔ 0 < (planeOrbitChart P x q).2.val := by
  apply descendedChart_positive (planeFace_covering P) x _ (planeOrbitInterior P) _ q hq
  intro y hy
  rw [planeOrbitInterior_preimage]
  exact planeProductChart_positive P _ _ y hy

/-- Supported inward deformations on the genuine compact face quotient. -/
theorem lineOrbit_localInward (L : Line) (q : LineFaceOrbit L) :
    ∃ H : InwardHomotopy.LocalDeformation (lineOrbitInterior L),
      H.homotopy (1, q) ∈ lineOrbitInterior L := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  exact SupportedInward.exists_localDeformation (lineOrbitInterior L) (lineOrbitChart L x)
    (lineOrbitChart_positive L x) _ (lineOrbitChart_mem L x)

theorem planeOrbit_localInward (P : Plane) (q : PlaneFaceOrbit P) :
    ∃ H : InwardHomotopy.LocalDeformation (planeOrbitInterior P),
      H.homotopy (1, q) ∈ planeOrbitInterior P := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  exact SupportedInward.exists_localDeformation (planeOrbitInterior P) (planeOrbitChart P x)
    (planeOrbitChart_positive P x) _ (planeOrbitChart_mem P x)

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
