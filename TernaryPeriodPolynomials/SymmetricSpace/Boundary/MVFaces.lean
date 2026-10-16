module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVCoordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction Topology
open IntegralGL3Congruence SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix
open scoped Pointwise

/-- Actual rational full flags, with their incidence proof. -/
def Flag := {p : Line × Plane // incidence p.1 p.2}

def flagLabel (g : RationalGL) : Flag := ⟨(lineLabel g, planeLabel g), labels_incident g⟩
def flagFace (F : Flag) : Set Glued := lineFace F.val.1 ∩ planeFace F.val.2

theorem flagFace_nonempty (F : Flag) : (flagFace F).Nonempty :=
  (face_inter_nonempty_iff _ _).mpr F.property

theorem flagFace_closed (F : Flag) : IsClosed (flagFace F) :=
  (lineFace_closed _).inter (planeFace_closed _)

theorem flagFace_unique {F G : Flag} {x : Glued} (hF : x ∈ flagFace F) (hG : x ∈ flagFace G) : F = G :=
  Subtype.ext (Prod.ext (lineFace_unique hF.1 hG.1) (planeFace_unique hF.2 hG.2))

theorem flagFace_injective : Function.Injective flagFace := by
  intro F G he
  obtain ⟨x, hx⟩ := flagFace_nonempty F
  exact flagFace_unique hx (he ▸ hx)

theorem flagFace_chart_iff (g : RationalGL) (p : Corner) (F : Flag) :
    chart g p ∈ flagFace F ↔ (p.2.1.val = 0 ∧ p.2.2.val = 0) ∧ flagLabel g = F := by
  change (chart g p ∈ lineFace F.val.1 ∧ chart g p ∈ planeFace F.val.2) ↔ _
  rw [lineFace_chart_iff, planeFace_chart_iff]
  constructor
  · rintro ⟨⟨h1, hL⟩, ⟨h2, hP⟩⟩
    exact ⟨⟨h1, h2⟩, Subtype.ext (Prod.ext hL hP)⟩
  · rintro ⟨⟨h1, h2⟩, he⟩
    exact ⟨⟨h1, congrArg (fun F : Flag => F.val.1) he⟩,
      ⟨h2, congrArg (fun F : Flag => F.val.2) he⟩⟩

/-- Every actual rational corner chart meets at most one full-flag face. -/
theorem flagFaces_locallyFinite : LocallyFinite flagFace := by
  intro x
  obtain ⟨g, p, rfl⟩ := chart_jointly_surjective x
  refine ⟨Set.range (chart g), (chart_range_open g).mem_nhds ⟨p, rfl⟩,
    (Set.finite_singleton (flagLabel g)).subset ?_⟩
  rintro F ⟨y, hy, q, rfl⟩
  exact ((flagFace_chart_iff g q F).mp hy).2.symm

theorem flagFace_union_closed (S : Set Flag) : IsClosed (⋃ F : S, flagFace F.val) :=
  (flagFaces_locallyFinite.comp_injective Subtype.val_injective).isClosed_iUnion
    (fun F => flagFace_closed F.val)

def lineSide : Set BoundaryCover := Subtype.val ⁻¹' (⋃ L : Line, lineFace L)
def planeSide : Set BoundaryCover := Subtype.val ⁻¹' (⋃ P : Plane, planeFace P)
def cornerLocus : Set BoundaryCover := lineSide ∩ planeSide

theorem lineSide_closed : IsClosed lineSide :=
  (lineFaces_locallyFinite.isClosed_iUnion lineFace_closed).preimage continuous_subtype_val

theorem planeSide_closed : IsClosed planeSide :=
  (planeFaces_locallyFinite.isClosed_iUnion planeFace_closed).preimage continuous_subtype_val

theorem cornerLocus_closed : IsClosed cornerLocus := lineSide_closed.inter planeSide_closed

theorem sides_cover : lineSide ∪ planeSide = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  have h := (boundary_iff_faces x.val).mp x.property
  simpa only [lineSide, planeSide, Set.mem_union, Set.mem_preimage, Set.mem_iUnion] using h

theorem cornerLocus_iff (x : BoundaryCover) : x ∈ cornerLocus ↔ ∃ F : Flag, x.val ∈ flagFace F := by
  simp only [cornerLocus, lineSide, planeSide, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨L, hL⟩, ⟨P, hP⟩⟩
    exact ⟨⟨(L, P), face_labels_incident hL hP⟩, hL, hP⟩
  · rintro ⟨F, hF⟩
    exact ⟨⟨F.val.1, hF.1⟩, ⟨F.val.2, hF.2⟩⟩

/-- Exact signed-normal side criteria for the actual closed boundary pieces. -/
theorem signedParam_lineSide (g : RationalGL) (p : SignedModel) :
    signedParam g p ∈ lineSide ↔ 0 ≤ p.2 := by
  simp only [lineSide, Set.mem_preimage, Set.mem_iUnion]
  simp only [signedParam_line_iff]
  exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨lineLabel g, h, rfl⟩⟩

theorem signedParam_planeSide (g : RationalGL) (p : SignedModel) :
    signedParam g p ∈ planeSide ↔ p.2 ≤ 0 := by
  simp only [planeSide, Set.mem_preimage, Set.mem_iUnion]
  simp only [signedParam_plane_iff]
  exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨planeLabel g, h, rfl⟩⟩

theorem signedParam_cornerLocus (g : RationalGL) (p : SignedModel) :
    signedParam g p ∈ cornerLocus ↔ p.2 = 0 := by
  change (signedParam g p ∈ lineSide ∧ signedParam g p ∈ planeSide) ↔ _
  rw [signedParam_lineSide, signedParam_planeSide]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

def flagAction (a : principalSix) (F : Flag) : Flag :=
  ⟨(OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a.val) F.val.1,
    OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a.val) F.val.2),
    (OrdinaryFullAction.incidence_action_iff _ _ _).mpr F.property⟩

theorem flagFace_image (a : principalSix) (F : Flag) :
    (fun x : Glued => a • x) '' flagFace F = flagFace (flagAction a F) := by
  change (fun x : Glued => a • x) '' (lineFace F.val.1 ∩ planeFace F.val.2) = _
  rw [Set.image_inter (MulAction.injective a), principalSix_lineFace_image, principalSix_planeFace_image]
  rfl

/-- Same-corner intersections force stabilization of the entire actual corner. -/
theorem flagFace_block (F : Flag) (a : principalSix) (x : Glued)
    (hx : x ∈ flagFace F) (ha : a • x ∈ flagFace F) :
    a ∈ MulAction.stabilizer principalSix (flagFace F) := by
  have hm : a • x ∈ flagFace (flagAction a F) := by rw [←flagFace_image]; exact ⟨x, hx, rfl⟩
  have he := flagFace_unique hm ha
  change (fun y : Glued => a • y) '' flagFace F = flagFace F
  rw [flagFace_image, he]

end TernaryPoly.SymmetricSpaceBoundaryMV
