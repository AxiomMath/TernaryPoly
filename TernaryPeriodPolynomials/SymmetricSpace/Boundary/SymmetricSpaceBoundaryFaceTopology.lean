module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceModelsCoordinates
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology

/-- Closed line-chart coordinates, with the first root fixed to zero. -/
def closedLineCoordinates : ClosedFaceModel ≃ₜ {p : Corner | p.2.1.val = 0} where
  toFun p := ⟨(p.1, zeroRoot, p.2), rfl⟩
  invFun p := (p.val.1, p.val.2.2)
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact Prod.ext (Subtype.ext p.property.symm) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Closed plane-chart coordinates, with the second root fixed to zero. -/
def closedPlaneCoordinates : ClosedFaceModel ≃ₜ {p : Corner | p.2.2.val = 0} where
  toFun p := ⟨(p.1, p.2, zeroRoot), rfl⟩
  invFun p := (p.val.1, p.val.2.1)
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact Prod.ext rfl (Subtype.ext p.property.symm)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual closed-face map with its inherited subspace topology. -/
def lineParam (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    ClosedFaceModel → lineFace L := fun p =>
  ⟨chart g (closedLineCoordinates p).val, (lineFace_chart_iff _ _ _).mpr ⟨rfl, hg⟩⟩

def planeParam (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    ClosedFaceModel → planeFace P := fun p =>
  ⟨chart g (closedPlaneCoordinates p).val, (planeFace_chart_iff _ _ _).mpr ⟨rfl, hg⟩⟩

theorem lineParam_isEmbedding (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    IsEmbedding (lineParam L g hg) :=
  ((chart_isOpenEmbedding g).isEmbedding.comp
    (IsEmbedding.subtypeVal.comp closedLineCoordinates.isEmbedding)).codRestrict _ _

theorem planeParam_isEmbedding (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    IsEmbedding (planeParam P g hg) :=
  ((chart_isOpenEmbedding g).isEmbedding.comp
    (IsEmbedding.subtypeVal.comp closedPlaneCoordinates.isEmbedding)).codRestrict _ _

/-- A restricted chart has exactly the original chart range intersected with the face. -/
theorem lineParam_range (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    Set.range (lineParam L g hg) = Subtype.val ⁻¹' Set.range (chart g) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(closedLineCoordinates p).val, rfl⟩
  · rintro ⟨p, hp⟩
    have hz : p.2.1.val = 0 := ((lineFace_chart_iff L g p).mp (hp ▸ x.property)).1
    refine ⟨closedLineCoordinates.symm ⟨p, hz⟩, Subtype.ext ?_⟩
    change chart g (closedLineCoordinates (closedLineCoordinates.symm ⟨p, hz⟩)).val = x.val
    simpa only [Homeomorph.apply_symm_apply] using hp

theorem planeParam_range (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    Set.range (planeParam P g hg) = Subtype.val ⁻¹' Set.range (chart g) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(closedPlaneCoordinates p).val, rfl⟩
  · rintro ⟨p, hp⟩
    have hz : p.2.2.val = 0 := ((planeFace_chart_iff P g p).mp (hp ▸ x.property)).1
    refine ⟨closedPlaneCoordinates.symm ⟨p, hz⟩, Subtype.ext ?_⟩
    change chart g (closedPlaneCoordinates (closedPlaneCoordinates.symm ⟨p, hz⟩)).val = x.val
    simpa only [Homeomorph.apply_symm_apply] using hp

/-- Restricting to the full closed face gives an open embedding into that face. -/
theorem lineParam_isOpenEmbedding (L : Line) (g : RationalGL) (hg : lineLabel g = L) :
    IsOpenEmbedding (lineParam L g hg) := by
  refine ⟨lineParam_isEmbedding L g hg, ?_⟩
  rw [lineParam_range]
  exact (chart_range_open g).preimage continuous_subtype_val

theorem planeParam_isOpenEmbedding (P : Plane) (g : RationalGL) (hg : planeLabel g = P) :
    IsOpenEmbedding (planeParam P g hg) := by
  refine ⟨planeParam_isEmbedding P g hg, ?_⟩
  rw [planeParam_range]
  exact (chart_range_open g).preimage continuous_subtype_val

/-- A height-first identification with the standard four-dimensional half-space. -/
def faceHalfSpaceHomeomorph : ClosedFaceModel ≃ₜ EuclideanHalfSpace 4 where
  toFun p := ⟨WithLp.toLp 2 ![p.2.val, p.1 0, p.1 1, p.1 2], p.2.property⟩
  invFun p := (![p.val 1, p.val 2, p.val 3], ⟨p.val 0, p.property⟩)
  left_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp (by fun_prop)
  continuous_invFun := by fun_prop

@[simp] theorem faceHalfSpace_height (p : ClosedFaceModel) :
    (faceHalfSpaceHomeomorph p).val 0 = p.2.val := rfl

/-- The height is positive exactly on the actual open line stratum. -/
theorem lineParam_positive (L : Line) (g : RationalGL) (hg : lineLabel g = L)
    (p : ClosedFaceModel) :
    (lineParam L g hg p).val ∈ openLineFace L ↔ 0 < p.2.val := by
  rw [lineParam, openLineFace_chart_iff]
  change ((0 : ℝ) = 0 ∧ 0 < p.2.val) ∧ lineLabel g = L ↔ _
  simp [hg]

theorem planeParam_positive (P : Plane) (g : RationalGL) (hg : planeLabel g = P)
    (p : ClosedFaceModel) :
    (planeParam P g hg p).val ∈ openPlaneFace P ↔ 0 < p.2.val := by
  rw [planeParam, openPlaneFace_chart_iff]
  change (0 < p.2.val ∧ (0 : ℝ) = 0) ∧ planeLabel g = P ↔ _
  simp [hg]

/-- The boundary of this line half-space chart is exactly its incident flag face. -/
theorem lineParam_boundary (L : Line) (g : RationalGL) (hg : lineLabel g = L)
    (p : ClosedFaceModel) :
    (∃ P, incidence L P ∧ (lineParam L g hg p).val ∈ planeFace P) ↔ p.2.val = 0 := by
  constructor
  · rintro ⟨P, _, hp⟩
    exact ((planeFace_chart_iff P g _).mp hp).1
  · intro hp
    refine ⟨planeLabel g, ?_, (planeFace_chart_iff _ _ _).mpr ⟨hp, rfl⟩⟩
    rw [←hg]
    exact labels_incident g

theorem planeParam_boundary (P : Plane) (g : RationalGL) (hg : planeLabel g = P)
    (p : ClosedFaceModel) :
    (∃ L, incidence L P ∧ (planeParam P g hg p).val ∈ lineFace L) ↔ p.2.val = 0 := by
  constructor
  · rintro ⟨L, _, hp⟩
    exact ((lineFace_chart_iff L g _).mp hp).1
  · intro hp
    refine ⟨lineLabel g, ?_, (lineFace_chart_iff _ _ _).mpr ⟨hp, rfl⟩⟩
    rw [←hg]
    exact labels_incident g

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
