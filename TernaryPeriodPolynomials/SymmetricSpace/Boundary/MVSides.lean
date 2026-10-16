module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVAssembly

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology OrdinaryIncidence SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction IntegralGL3Congruence
  SymmetricSpaceBordifiedQuotient
open scoped Pointwise

theorem lineSide_smul (a : principalSix) {x : BoundaryCover} (hx : x∈lineSide) : a • x∈lineSide := by
  obtain ⟨L,hL⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a.val) L,?_⟩
  rw [←principalSix_lineFace_image]
  exact ⟨x.val,hL,rfl⟩

theorem planeSide_smul (a : principalSix) {x : BoundaryCover} (hx : x∈planeSide) : a • x∈planeSide := by
  obtain ⟨P,hP⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a.val) P,?_⟩
  rw [←principalSix_planeFace_image]
  exact ⟨x.val,hP,rfl⟩

theorem boundaryProjection_invariant_preimage (S : Set BoundaryCover)
    (hS : ∀ (a : principalSix) x, x∈S → a • x∈S) :
    boundaryProjection ⁻¹' (boundaryProjection '' S)=S := by
  ext x
  constructor
  · rintro ⟨y,hy,he⟩
    obtain ⟨a,ha⟩ := boundaryQuotientCovering.apply_eq_iff_mem_orbit.mp he.symm
    exact ha ▸ hS a y hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem boundaryProjection_openQuotient : IsOpenQuotientMap boundaryProjection :=
  ⟨boundaryProjection_surjective,boundaryCovering.continuous,boundaryCovering.isOpenMap⟩

def lineBase : Set BoundaryBase := boundaryProjection '' lineSide
def planeBase : Set BoundaryBase := boundaryProjection '' planeSide

theorem boundaryProjection_mem_line (x : BoundaryCover) :
    boundaryProjection x∈lineBase ↔ x∈lineSide :=
  Set.ext_iff.mp (boundaryProjection_invariant_preimage lineSide (fun a _ h => lineSide_smul a h)) x

theorem boundaryProjection_mem_plane (x : BoundaryCover) :
    boundaryProjection x∈planeBase ↔ x∈planeSide :=
  Set.ext_iff.mp (boundaryProjection_invariant_preimage planeSide (fun a _ h => planeSide_smul a h)) x

theorem lineBase_closed : IsClosed lineBase := by
  apply boundaryProjection_openQuotient.isQuotientMap.isCoinducing.isClosed_preimage.mp
  change IsClosed (boundaryProjection ⁻¹' (boundaryProjection '' lineSide))
  rw [boundaryProjection_invariant_preimage lineSide (fun a _ h => lineSide_smul a h)]
  exact lineSide_closed

theorem planeBase_closed : IsClosed planeBase := by
  apply boundaryProjection_openQuotient.isQuotientMap.isCoinducing.isClosed_preimage.mp
  change IsClosed (boundaryProjection ⁻¹' (boundaryProjection '' planeSide))
  rw [boundaryProjection_invariant_preimage planeSide (fun a _ h => planeSide_smul a h)]
  exact planeSide_closed

theorem bases_cover : lineBase ∪ planeBase=Set.univ := by
  ext x
  obtain ⟨y,rfl⟩ := boundaryProjection_surjective x
  change (boundaryProjection y∈lineBase ∨ boundaryProjection y∈planeBase) ↔ True
  rw [boundaryProjection_mem_line,boundaryProjection_mem_plane]
  exact iff_true_intro (sides_cover.ge (Set.mem_univ y))

theorem bases_inter : lineBase ∩ planeBase=cornerBase := by
  ext x
  obtain ⟨y,rfl⟩ := boundaryProjection_surjective x
  rw [Set.mem_inter_iff,boundaryProjection_mem_line,boundaryProjection_mem_plane,boundaryProjection_mem_corner]
  rfl

theorem flagCollarBase_line (F : Flag) (x : FlagFaceOrbit F) (t : ℝ) :
    flagCollarBase F (x,t)∈lineBase ↔ 0≤t := by
  induction x using Quotient.inductionOn with | _ x =>
  exact (boundaryProjection_mem_line _).trans
    (signedParam_lineSide (chosenFrame F) ((flagCoordinates F).symm x,t))

theorem flagCollarBase_plane (F : Flag) (x : FlagFaceOrbit F) (t : ℝ) :
    flagCollarBase F (x,t)∈planeBase ↔ t≤0 := by
  induction x using Quotient.inductionOn with | _ x =>
  exact (boundaryProjection_mem_plane _).trans
    (signedParam_planeSide (chosenFrame F) ((flagCoordinates F).symm x,t))

theorem assembledCollar_line (x : CornerSource) (t : ℝ) :
    assembledCollar (x,t)∈lineBase ↔ 0≤t := flagCollarBase_line _ _ _

theorem assembledCollar_plane (x : CornerSource) (t : ℝ) :
    assembledCollar (x,t)∈planeBase ↔ t≤0 := flagCollarBase_plane _ _ _

/-- One radius, chosen only after the global compact-source embedding theorem. -/
def collarRadius : ℝ := assembledCollar_exists_strip.choose

theorem collarRadius_pos : 0<collarRadius := assembledCollar_exists_strip.choose_spec.1

abbrev CollarStrip := (Set.univ ×ˢ Set.Ioo (-collarRadius) collarRadius : Set (CornerSource × ℝ))

def collarParam : CollarStrip → BoundaryBase := CollarStrip.domRestrict assembledCollar

theorem collarParam_isOpenEmbedding : IsOpenEmbedding collarParam :=
  assembledCollar_exists_strip.choose_spec.2

def collarNeighborhood : Set BoundaryBase := Set.range collarParam

theorem collarNeighborhood_open : IsOpen collarNeighborhood := collarParam_isOpenEmbedding.isOpen_range

def collarHomeomorph : CollarStrip ≃ₜ collarNeighborhood := collarParam_isOpenEmbedding.isEmbedding.toHomeomorph

@[simp] theorem collarHomeomorph_val (x : CollarStrip) : (collarHomeomorph x).val=collarParam x := rfl

def collarZero (x : CornerSource) : CollarStrip := ⟨(x,0),⟨Set.mem_univ _,by
  constructor <;> linarith [collarRadius_pos]⟩⟩

theorem cornerBase_subset_collar : cornerBase ⊆ collarNeighborhood := by
  intro x hx
  obtain ⟨q,hq⟩ := cornerSourceToBase_surjective ⟨x,hx⟩
  exact ⟨collarZero q,congrArg Subtype.val hq⟩

@[simp] theorem collarParam_line (x : CollarStrip) : collarParam x∈lineBase ↔ 0≤x.val.2 :=
  assembledCollar_line _ _

@[simp] theorem collarParam_plane (x : CollarStrip) : collarParam x∈planeBase ↔ x.val.2≤0 :=
  assembledCollar_plane _ _

@[simp] theorem collarParam_corner (x : CollarStrip) : collarParam x∈cornerBase ↔ x.val.2=0 :=
  assembledCollar_corner _ _

end TernaryPoly.SymmetricSpaceBoundaryMV
