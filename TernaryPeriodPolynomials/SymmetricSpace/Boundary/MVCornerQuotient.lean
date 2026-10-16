module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVFaces

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open OrdinaryIncidence SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction Topology
open IntegralGL3Congruence SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix
open scoped Pointwise

def flagLabelOrbit (F : Flag) : Set Flag := Set.range (fun a : principalSix => flagAction a F)

theorem projection_flagFace_preimage (F : Flag) :
    projection principalSix ⁻¹' (projection principalSix '' flagFace F) =
      ⋃ G : flagLabelOrbit F, flagFace G.val := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := Quotient.exact he.symm
    apply Set.mem_iUnion.mpr
    refine ⟨⟨_, ⟨a, rfl⟩⟩, ?_⟩
    rw [←flagFace_image]
    exact ⟨y, hy, ha⟩
  · intro hx
    obtain ⟨⟨G, a, rfl⟩, hG⟩ := Set.mem_iUnion.mp hx
    rw [←flagFace_image] at hG
    obtain ⟨y, hy, rfl⟩ := hG
    exact ⟨y, hy, (projection_smul principalSix a y).symm⟩

theorem projection_flagFace_closed (F : Flag) : IsClosed (projection principalSix '' flagFace F) := by
  apply (projection_openQuotient principalSix).isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [projection_flagFace_preimage]
  exact flagFace_union_closed _

theorem projection_flagFace_compact (F : Flag) : IsCompact (projection principalSix '' flagFace F) := by
  let := SymmetricSpaceCompactBordification.quotient_compact principalSix
  exact (projection_flagFace_closed F).isCompact

theorem flagFace_openInSaturation (F : Flag) :
    IsOpen (Subtype.val ⁻¹' flagFace F :
      Set (RestrictedQuotient.saturation (G := principalSix) (flagFace F))) := by
  let A : Set Glued := ⋃ G : {G : Flag | G ≠ F}, flagFace G.val
  have hA : IsClosed A := flagFace_union_closed {G | G ≠ F}
  have he : (Subtype.val ⁻¹' flagFace F :
      Set (RestrictedQuotient.saturation (G := principalSix) (flagFace F))) =
      (Subtype.val ⁻¹' A)ᶜ := by
    ext x
    change x.val ∈ flagFace F ↔ x.val ∉ A
    constructor
    · intro hx ha
      obtain ⟨G, hG⟩ := Set.mem_iUnion.mp ha
      exact G.property (flagFace_unique hG hx)
    · intro hx
      have hs := x.property
      change x.val ∈ projection principalSix ⁻¹' (projection principalSix '' flagFace F) at hs
      rw [projection_flagFace_preimage] at hs
      obtain ⟨⟨G, _⟩, hG⟩ := Set.mem_iUnion.mp hs
      by_cases he : G = F
      · simpa only [he] using hG
      · exact False.elim (hx (Set.mem_iUnion.mpr ⟨⟨G, he⟩, hG⟩))
  rw [he]
  exact (hA.preimage continuous_subtype_val).isOpen_compl

abbrev FlagFaceOrbit (F : Flag) := RestrictedQuotient.FaceOrbit (G := principalSix) (flagFace F)

/-- The actual corner-stabilizer quotient is its literal compact corner image. -/
def flagFaceQuotientHomeomorph (F : Flag) :
    FlagFaceOrbit F ≃ₜ (projection principalSix '' flagFace F) :=
  RestrictedQuotient.quotientImageHomeomorph (flagFace F) (flagFace_block F)
    (flagFace_openInSaturation F)

instance flagFaceOrbit_compact (F : Flag) : CompactSpace (FlagFaceOrbit F) := by
  let := isCompact_iff_compactSpace.mp (projection_flagFace_compact F)
  exact (flagFaceQuotientHomeomorph F).symm.compactSpace

instance flagFaceOrbit_hausdorff (F : Flag) : T2Space (FlagFaceOrbit F) := by
  let := SymmetricSpaceCompactBordification.quotient_hausdorff principalSix
  exact (flagFaceQuotientHomeomorph F).isEmbedding.t2Space

def allCorners : Set Glued := ⋃ F : Flag, flagFace F

theorem allCorners_closed : IsClosed allCorners := flagFaces_locallyFinite.isClosed_iUnion flagFace_closed

theorem cornerLocus_eq_preimage : cornerLocus = Subtype.val ⁻¹' allCorners := by
  ext x
  simpa only [allCorners, Set.mem_preimage, Set.mem_iUnion] using cornerLocus_iff x

theorem allCorners_smul (a : principalSix) {x : Glued} (hx : x ∈ allCorners) : a • x ∈ allCorners := by
  obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨flagAction a F, ?_⟩
  rw [←flagFace_image]
  exact ⟨x, hF, rfl⟩

theorem projection_allCorners_preimage :
    projection principalSix ⁻¹' (projection principalSix '' allCorners) = allCorners := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := Quotient.exact he.symm
    have h := allCorners_smul a hy
    exact ha ▸ h
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem projection_allCorners_closed : IsClosed (projection principalSix '' allCorners) := by
  apply (projection_openQuotient principalSix).isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [projection_allCorners_preimage]
  exact allCorners_closed

theorem allCorners_mem_boundary {x : Glued} (hx : x ∈ allCorners) : x ∈ upstairsBoundary := by
  obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hx
  exact (boundary_iff_faces x).mpr (Or.inl ⟨F.val.1, hF.1⟩)

/-- Literal corner image in the actual boundary quotient. -/
def cornerBase : Set BoundaryBase := boundaryProjection '' cornerLocus

theorem cornerBase_eq_preimage :
    cornerBase = Subtype.val ⁻¹' (projection principalSix '' allCorners) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, (Set.ext_iff.mp cornerLocus_eq_preimage x).mp hx, rfl⟩
  · rintro ⟨x, hx, he⟩
    refine ⟨⟨x, allCorners_mem_boundary hx⟩, ?_, Subtype.ext he⟩
    exact (Set.ext_iff.mp cornerLocus_eq_preimage _).mpr hx

theorem cornerBase_closed : IsClosed cornerBase := by
  rw [cornerBase_eq_preimage]
  exact projection_allCorners_closed.preimage continuous_subtype_val

/-- The whole actual corner locus downstairs is compact, including all arithmetic flag orbits. -/
theorem cornerBase_compact : IsCompact cornerBase := by
  let := SymmetricSpaceCompactBordification.quotient_compact principalSix
  let := isCompact_iff_compactSpace.mp (boundary_closed principalSix).isCompact
  exact cornerBase_closed.isCompact

end TernaryPoly.SymmetricSpaceBoundaryMV
