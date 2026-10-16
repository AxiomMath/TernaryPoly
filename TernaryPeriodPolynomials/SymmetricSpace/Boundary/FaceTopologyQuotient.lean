module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyQuotientGeneral

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology
open IntegralGL3Congruence SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix
open scoped Pointwise

/-- A principal-six translate which meets a line face must stabilize that whole face. -/
theorem lineFace_block (L : Line) (a : principalSix) (x : Glued)
    (hx : x ∈ lineFace L) (ha : a • x ∈ lineFace L) :
    a ∈ MulAction.stabilizer principalSix (lineFace L) := by
  have hm : a • x ∈ lineFace
      (OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a.val) L) := by
    rw [←principalSix_lineFace_image]
    exact ⟨x, hx, rfl⟩
  have he := lineFace_unique hm ha
  change (fun y : Glued => a • y) '' lineFace L = lineFace L
  rw [principalSix_lineFace_image, he]

theorem planeFace_block (P : Plane) (a : principalSix) (x : Glued)
    (hx : x ∈ planeFace P) (ha : a • x ∈ planeFace P) :
    a ∈ MulAction.stabilizer principalSix (planeFace P) := by
  have hm : a • x ∈ planeFace
      (OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a.val) P) := by
    rw [←principalSix_planeFace_image]
    exact ⟨x, hx, rfl⟩
  have he := planeFace_unique hm ha
  change (fun y : Glued => a • y) '' planeFace P = planeFace P
  rw [principalSix_planeFace_image, he]

/-- An individual line face is open within its entire arithmetic saturation. -/
theorem lineFace_openInSaturation (L : Line) :
    IsOpen (Subtype.val ⁻¹' lineFace L :
      Set (RestrictedQuotient.saturation (G := principalSix) (lineFace L))) := by
  let A : Set Glued := ⋃ M : {M : Line | M ≠ L}, lineFace M.val
  have hA : IsClosed A := lineFace_union_closed {M | M ≠ L}
  have he : (Subtype.val ⁻¹' lineFace L :
      Set (RestrictedQuotient.saturation (G := principalSix) (lineFace L))) =
      (Subtype.val ⁻¹' A)ᶜ := by
    ext x
    change x.val ∈ lineFace L ↔ x.val ∉ A
    constructor
    · intro hx ha
      obtain ⟨M, hm⟩ := Set.mem_iUnion.mp ha
      exact M.property (lineFace_unique hm hx)
    · intro hx
      have hs := x.property
      change x.val ∈ projection principalSix ⁻¹' (projection principalSix '' lineFace L) at hs
      rw [projection_lineFace_preimage] at hs
      obtain ⟨⟨M, _⟩, hm⟩ := Set.mem_iUnion.mp hs
      by_cases he : M = L
      · simpa only [he] using hm
      · exact False.elim (hx (Set.mem_iUnion.mpr ⟨⟨M, he⟩, hm⟩))
  rw [he]
  exact (hA.preimage continuous_subtype_val).isOpen_compl

theorem planeFace_openInSaturation (P : Plane) :
    IsOpen (Subtype.val ⁻¹' planeFace P :
      Set (RestrictedQuotient.saturation (G := principalSix) (planeFace P))) := by
  let A : Set Glued := ⋃ Q : {Q : Plane | Q ≠ P}, planeFace Q.val
  have hA : IsClosed A := planeFace_union_closed {Q | Q ≠ P}
  have he : (Subtype.val ⁻¹' planeFace P :
      Set (RestrictedQuotient.saturation (G := principalSix) (planeFace P))) =
      (Subtype.val ⁻¹' A)ᶜ := by
    ext x
    change x.val ∈ planeFace P ↔ x.val ∉ A
    constructor
    · intro hx ha
      obtain ⟨Q, hq⟩ := Set.mem_iUnion.mp ha
      exact Q.property (planeFace_unique hq hx)
    · intro hx
      have hs := x.property
      change x.val ∈ projection principalSix ⁻¹' (projection principalSix '' planeFace P) at hs
      rw [projection_planeFace_preimage] at hs
      obtain ⟨⟨Q, _⟩, hq⟩ := Set.mem_iUnion.mp hs
      by_cases he : Q = P
      · simpa only [he] using hq
      · exact False.elim (hx (Set.mem_iUnion.mpr ⟨⟨Q, he⟩, hq⟩))
  rw [he]
  exact (hA.preimage continuous_subtype_val).isOpen_compl

abbrev LineFaceOrbit (L : Line) := RestrictedQuotient.FaceOrbit (G := principalSix) (lineFace L)
abbrev PlaneFaceOrbit (P : Plane) := RestrictedQuotient.FaceOrbit (G := principalSix) (planeFace P)

/-- The true face-stabilizer quotient is homeomorphic to its compact image in BordifiedOrbit. -/
def lineFaceQuotientHomeomorph (L : Line) :
    LineFaceOrbit L ≃ₜ (projection principalSix '' lineFace L) :=
  RestrictedQuotient.quotientImageHomeomorph (lineFace L) (lineFace_block L)
    (lineFace_openInSaturation L)

def planeFaceQuotientHomeomorph (P : Plane) :
    PlaneFaceOrbit P ≃ₜ (projection principalSix '' planeFace P) :=
  RestrictedQuotient.quotientImageHomeomorph (planeFace P) (planeFace_block P)
    (planeFace_openInSaturation P)

@[simp] theorem lineFaceQuotientHomeomorph_mk (L : Line) (x : lineFace L) :
    (lineFaceQuotientHomeomorph L (RestrictedQuotient.faceProjection (lineFace L) x)).val =
      projection principalSix x.val := rfl

@[simp] theorem planeFaceQuotientHomeomorph_mk (P : Plane) (x : planeFace P) :
    (planeFaceQuotientHomeomorph P (RestrictedQuotient.faceProjection (planeFace P) x)).val =
      projection principalSix x.val := rfl

instance lineFaceOrbit_compact (L : Line) : CompactSpace (LineFaceOrbit L) := by
  let := isCompact_iff_compactSpace.mp (projection_lineFace_compact L)
  exact (lineFaceQuotientHomeomorph L).symm.compactSpace

instance planeFaceOrbit_compact (P : Plane) : CompactSpace (PlaneFaceOrbit P) := by
  let := isCompact_iff_compactSpace.mp (projection_planeFace_compact P)
  exact (planeFaceQuotientHomeomorph P).symm.compactSpace

instance lineFaceOrbit_hausdorff (L : Line) : T2Space (LineFaceOrbit L) := by
  let := SymmetricSpaceCompactBordification.quotient_hausdorff principalSix
  exact (lineFaceQuotientHomeomorph L).isEmbedding.t2Space

instance planeFaceOrbit_hausdorff (P : Plane) : T2Space (PlaneFaceOrbit P) := by
  let := SymmetricSpaceCompactBordification.quotient_hausdorff principalSix
  exact (planeFaceQuotientHomeomorph P).isEmbedding.t2Space

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
