module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyCovering

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology
open IntegralGL3Congruence
open scoped Pointwise

/-- Actual rational action transports whole open line strata. -/
theorem openLineFace_action_iff (a : RationalGL) (L : Line) (x : Glued) :
    leftAction a x ∈ openLineFace (OrdinaryFullAction.lineAction a L) ↔ x ∈ openLineFace L := by
  obtain ⟨g, p, rfl⟩ := chart_jointly_surjective x
  rw [leftAction_chart, openLineFace_chart_iff, openLineFace_chart_iff]
  change (p ∈ lineLocus ∧ OrdinaryFullAction.lineAction (a * g) standardLine =
    OrdinaryFullAction.lineAction a L) ↔ _
  rw [lineAction_mul]
  exact and_congr_right (fun _ => (OrdinaryFullAction.lineAction a).injective.eq_iff)

theorem openPlaneFace_action_iff (a : RationalGL) (P : Plane) (x : Glued) :
    leftAction a x ∈ openPlaneFace (OrdinaryFullAction.planeAction a P) ↔ x ∈ openPlaneFace P := by
  obtain ⟨g, p, rfl⟩ := chart_jointly_surjective x
  rw [leftAction_chart, openPlaneFace_chart_iff, openPlaneFace_chart_iff]
  change (p ∈ planeLocus ∧ OrdinaryFullAction.planeAction (a * g) standardPlane =
    OrdinaryFullAction.planeAction a P) ↔ _
  rw [planeAction_mul]
  exact and_congr_right (fun _ => (OrdinaryFullAction.planeAction a).injective.eq_iff)

def lineFaceInterior (L : Line) : Set (lineFace L) := Subtype.val ⁻¹' openLineFace L
def planeFaceInterior (P : Plane) : Set (planeFace P) := Subtype.val ⁻¹' openPlaneFace P

theorem lineFaceInterior_open (L : Line) : IsOpen (lineFaceInterior L) := by
  have he : lineFaceInterior L = (Subtype.val ⁻¹' (⋃ P : Plane, planeFace P))ᶜ := by
    ext x
    simp [lineFaceInterior, openLineFace]
  rw [he]
  exact ((planeFaces_locallyFinite.isClosed_iUnion planeFace_closed).preimage
    continuous_subtype_val).isOpen_compl

theorem planeFaceInterior_open (P : Plane) : IsOpen (planeFaceInterior P) := by
  have he : planeFaceInterior P = (Subtype.val ⁻¹' (⋃ L : Line, lineFace L))ᶜ := by
    ext x
    simp [planeFaceInterior, openPlaneFace]
  rw [he]
  exact ((lineFaces_locallyFinite.isClosed_iUnion lineFace_closed).preimage
    continuous_subtype_val).isOpen_compl

/-- The actual line-face stabilizer preserves precisely its open stratum. -/
theorem lineFaceInterior_smul (L : Line) (a : MulAction.stabilizer principalSix (lineFace L))
    (x : lineFace L) (hx : x ∈ lineFaceInterior L) : a • x ∈ lineFaceInterior L := by
  have he : OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a.val.val) L = L := by
    apply lineFace_injective
    rw [←principalSix_lineFace_image]
    exact a.property
  have h := (openLineFace_action_iff (integralRational a.val.val) L x.val).mpr hx
  change a.val • x.val ∈ openLineFace L
  change a.val • x.val ∈ openLineFace
    (OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a.val.val) L) at h
  rwa [he] at h

theorem planeFaceInterior_smul (P : Plane) (a : MulAction.stabilizer principalSix (planeFace P))
    (x : planeFace P) (hx : x ∈ planeFaceInterior P) : a • x ∈ planeFaceInterior P := by
  have he : OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a.val.val) P = P := by
    apply planeFace_injective
    rw [←principalSix_planeFace_image]
    exact a.property
  have h := (openPlaneFace_action_iff (integralRational a.val.val) P x.val).mpr hx
  change a.val • x.val ∈ openPlaneFace P
  change a.val • x.val ∈ openPlaneFace
    (OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a.val.val) P) at h
  rwa [he] at h

def lineOrbitInterior (L : Line) : Set (LineFaceOrbit L) :=
  RestrictedQuotient.faceProjection (lineFace L) '' lineFaceInterior L

def planeOrbitInterior (P : Plane) : Set (PlaneFaceOrbit P) :=
  RestrictedQuotient.faceProjection (planeFace P) '' planeFaceInterior P

theorem lineOrbitInterior_open (L : Line) : IsOpen (lineOrbitInterior L) :=
  MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ (lineFaceInterior_open L)

theorem planeOrbitInterior_open (P : Plane) : IsOpen (planeOrbitInterior P) :=
  MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ (planeFaceInterior_open P)

/-- Exact upstairs interior, not merely an abstract homotopy-equivalent replacement. -/
theorem lineOrbitInterior_preimage (L : Line) :
    RestrictedQuotient.faceProjection (lineFace L) ⁻¹' lineOrbitInterior L = lineFaceInterior L := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := Quotient.exact he.symm
    have h := lineFaceInterior_smul L a y hy
    exact ha ▸ h
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem planeOrbitInterior_preimage (P : Plane) :
    RestrictedQuotient.faceProjection (planeFace P) ⁻¹' planeOrbitInterior P = planeFaceInterior P := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := Quotient.exact he.symm
    have h := planeFaceInterior_smul P a y hy
    exact ha ▸ h
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The upstairs interior subtype is literally the already-contractible open stratum. -/
def lineFaceInteriorHomeomorph (L : Line) : lineFaceInterior L ≃ₜ openLineFace L where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def planeFaceInteriorHomeomorph (P : Plane) : planeFaceInterior P ≃ₜ openPlaneFace P where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance lineFaceInterior_contractible (L : Line) : ContractibleSpace (lineFaceInterior L) :=
  (lineFaceInteriorHomeomorph L).contractibleSpace

instance planeFaceInterior_contractible (P : Plane) : ContractibleSpace (planeFaceInterior P) :=
  (planeFaceInteriorHomeomorph P).contractibleSpace

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
