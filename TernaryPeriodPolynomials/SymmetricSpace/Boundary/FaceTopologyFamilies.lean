module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyBoundary
public import TernaryPeriodPolynomials.SymmetricSpace.CompactBordification
public import Mathlib.Topology.LocallyFinite

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels Topology
open IntegralGL3Congruence SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix

/-- Every actual corner chart meets at most one rational line face. -/
theorem lineFaces_locallyFinite : LocallyFinite lineFace := by
  intro x
  obtain ⟨g, p, rfl⟩ := chart_jointly_surjective x
  refine ⟨Set.range (chart g), (chart_range_open g).mem_nhds ⟨p, rfl⟩,
    (Set.finite_singleton (lineLabel g)).subset ?_⟩
  rintro L ⟨y, hy, q, rfl⟩
  exact ((lineFace_chart_iff L g q).mp hy).2.symm

/-- The same local finiteness holds for the actual rational plane faces. -/
theorem planeFaces_locallyFinite : LocallyFinite planeFace := by
  intro x
  obtain ⟨g, p, rfl⟩ := chart_jointly_surjective x
  refine ⟨Set.range (chart g), (chart_range_open g).mem_nhds ⟨p, rfl⟩,
    (Set.finite_singleton (planeLabel g)).subset ?_⟩
  rintro P ⟨y, hy, q, rfl⟩
  exact ((planeFace_chart_iff P g q).mp hy).2.symm

/-- Any subfamily of line faces has closed union, including an infinite arithmetic orbit. -/
theorem lineFace_union_closed (S : Set Line) : IsClosed (⋃ L : S, lineFace L.val) :=
  (lineFaces_locallyFinite.comp_injective Subtype.val_injective).isClosed_iUnion
    (fun L => lineFace_closed L.val)

theorem planeFace_union_closed (S : Set Plane) : IsClosed (⋃ P : S, planeFace P.val) :=
  (planeFaces_locallyFinite.comp_injective Subtype.val_injective).isClosed_iUnion
    (fun P => planeFace_closed P.val)

/-- The literal orbit of the line label under principal level six. -/
def lineLabelOrbit (L : Line) : Set Line := Set.range
  (fun a : principalSix => OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a.val) L)

def planeLabelOrbit (P : Plane) : Set Plane := Set.range
  (fun a : principalSix => OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a.val) P)

/-- The full inverse image of the quotient face image is its actual arithmetic face saturation. -/
theorem projection_lineFace_preimage (L : Line) :
    projection principalSix ⁻¹' (projection principalSix '' lineFace L) =
      ⋃ M : lineLabelOrbit L, lineFace M.val := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := Quotient.exact he.symm
    apply Set.mem_iUnion.mpr
    refine ⟨⟨_, ⟨a, rfl⟩⟩, ?_⟩
    rw [←principalSix_lineFace_image a L]
    exact ⟨y, hy, ha⟩
  · intro hx
    obtain ⟨⟨M, a, rfl⟩, hM⟩ := Set.mem_iUnion.mp hx
    rw [←principalSix_lineFace_image a L] at hM
    obtain ⟨y, hy, rfl⟩ := hM
    exact ⟨y, hy, (projection_smul principalSix a y).symm⟩

theorem projection_planeFace_preimage (P : Plane) :
    projection principalSix ⁻¹' (projection principalSix '' planeFace P) =
      ⋃ Q : planeLabelOrbit P, planeFace Q.val := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha⟩ := Quotient.exact he.symm
    apply Set.mem_iUnion.mpr
    refine ⟨⟨_, ⟨a, rfl⟩⟩, ?_⟩
    rw [←principalSix_planeFace_image a P]
    exact ⟨y, hy, ha⟩
  · intro hx
    obtain ⟨⟨Q, a, rfl⟩, hQ⟩ := Set.mem_iUnion.mp hx
    rw [←principalSix_planeFace_image a P] at hQ
    obtain ⟨y, hy, rfl⟩ := hQ
    exact ⟨y, hy, (projection_smul principalSix a y).symm⟩

/-- The image of every closed line face is closed in the actual compact arithmetic quotient. -/
theorem projection_lineFace_closed (L : Line) :
    IsClosed (projection principalSix '' lineFace L) := by
  apply (projection_openQuotient principalSix).isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [projection_lineFace_preimage]
  exact lineFace_union_closed _

theorem projection_planeFace_closed (P : Plane) :
    IsClosed (projection principalSix '' planeFace P) := by
  apply (projection_openQuotient principalSix).isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [projection_planeFace_preimage]
  exact planeFace_union_closed _

/-- Compactness here concerns the literal face image; identifying the face-stabilizer quotient
with this image remains a separate topological comparison. -/
theorem projection_lineFace_compact (L : Line) :
    IsCompact (projection principalSix '' lineFace L) := by
  let := SymmetricSpaceCompactBordification.quotient_compact principalSix
  exact (projection_lineFace_closed L).isCompact

theorem projection_planeFace_compact (P : Plane) :
    IsCompact (projection principalSix '' planeFace P) := by
  let := SymmetricSpaceCompactBordification.quotient_compact principalSix
  exact (projection_planeFace_closed P).isCompact

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
