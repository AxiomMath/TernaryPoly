module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyQuotient

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology.RestrictedQuotient
open Topology
open scoped Pointwise
variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

omit [ContinuousConstSMul G X] in
/-- Finite compact transporters restrict to the actual set-stabilizer action on a subset. -/
theorem compact_transporters (F : Set X)
    (hfinite : ∀ C D : Set X, IsCompact C → IsCompact D →
      {g : G | ((g • ·) '' C ∩ D).Nonempty}.Finite)
    (C D : Set F) (hC : IsCompact C) (hD : IsCompact D) :
    {g : MulAction.stabilizer G F | ((g • ·) '' C ∩ D).Nonempty}.Finite := by
  apply Set.Finite.of_finite_image (f := Subtype.val)
  · apply (hfinite (Subtype.val '' C) (Subtype.val '' D)
      (hC.image continuous_subtype_val) (hD.image continuous_subtype_val)).subset
    rintro _ ⟨g, ⟨y, ⟨x, hx, hxy⟩, hy⟩, rfl⟩
    exact ⟨y.val, ⟨x.val, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩, ⟨y, hy, rfl⟩⟩
  · exact Subtype.val_injective.injOn

/-- The restricted free/proper action gives the genuine covering of the face quotient. -/
theorem covering (F : Set X) [LocallyCompactSpace F] [T2Space F]
    (hfinite : ∀ C D : Set X, IsCompact C → IsCompact D →
      {g : G | ((g • ·) '' C ∩ D).Nonempty}.Finite)
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    IsCoveringMap (faceProjection (G := G) F) :=
  SymmetricSpaceCovering.covering_of_finite_transporters (compact_transporters F hfinite)
    (fun g x hx => Subtype.ext (hfree g.val x.val (congrArg Subtype.val hx)))

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology.RestrictedQuotient

namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology
open OrdinaryIncidence SymmetricSpaceBoundaryFaces SymmetricSpaceRationalGluing
  IntegralGL3Congruence SymmetricSpaceBordifiedQuotient Topology

instance lineFace_locallyCompact (L : Line) : LocallyCompactSpace (lineFace L) :=
  (lineFace_closed L).locallyCompactSpace

instance planeFace_locallyCompact (P : Plane) : LocallyCompactSpace (planeFace P) :=
  (planeFace_closed P).locallyCompactSpace

/-- The literal quotient by the true principal-six line-face stabilizer is a covering. -/
theorem lineFace_covering (L : Line) :
    IsCoveringMap (RestrictedQuotient.faceProjection (G := principalSix) (lineFace L)) :=
  RestrictedQuotient.covering (lineFace L)
    (SymmetricSpaceCompactBordification.subgroup_compact_transporters principalSix)
    SymmetricSpaceCompactBordification.principalSix_free

theorem planeFace_covering (P : Plane) :
    IsCoveringMap (RestrictedQuotient.faceProjection (G := principalSix) (planeFace P)) :=
  RestrictedQuotient.covering (planeFace P)
    (SymmetricSpaceCompactBordification.subgroup_compact_transporters principalSix)
    SymmetricSpaceCompactBordification.principalSix_free

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology
