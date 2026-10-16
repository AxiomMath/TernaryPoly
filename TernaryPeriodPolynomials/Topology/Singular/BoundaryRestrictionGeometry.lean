module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticProper
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Covering
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section


noncomputable section
open CategoryTheory
namespace TernaryPoly.SingularBoundaryRestriction
open Topology SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- The literal complement of the positive-form locus upstairs. -/
def upstairsBoundary : Set Glued := (Set.range embedding)ᶜ

abbrev BoundaryCover := upstairsBoundary
abbrev BoundaryBase := boundary principalSix

/-- The actual upstairs boundary is precisely the preimage of the actual quotient boundary. -/
theorem boundary_iff (x : Glued) :
    x∈upstairsBoundary ↔ projection principalSix x∈boundary principalSix :=
  (Set.ext_iff.mp (projection_preimage_boundary principalSix) x).symm

instance boundaryAction : MulAction principalSix BoundaryCover where
  smul g x := ⟨g • x.val,(boundary_iff _).mpr (by
    rw [projection_smul]
    exact (boundary_iff _).mp x.property)⟩
  one_smul x := Subtype.ext (one_smul principalSix x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

@[simp] theorem boundary_smul_val (g : principalSix) (x : BoundaryCover) :
    (g • x).val=g • x.val := rfl

instance boundaryContinuous : ContinuousConstSMul principalSix BoundaryCover where
  continuous_const_smul g :=
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

/-- The whole literal quotient covering, bundled as a continuous map. -/
def wholeProjection : TopCat.of Glued ⟶ TopCat.of BordifiedOrbit :=
  TopCat.ofHom ⟨projection principalSix,projection_continuous principalSix⟩

theorem wholeQuotientCovering : IsQuotientCoveringMap wholeProjection principalSix :=
  SymmetricSpaceCovering.quotientCovering_of_finite_transporters
    (principalSix_compact_transporters SymmetricSpaceGluedArithmetic.compact_transporter_finite)
    (SymmetricSpaceBordifiedPrincipalSix.principalSix_fixed_eq_one
      SymmetricSpaceGluedArithmetic.compact_transporter_finite)

/-- The actual inclusion of the invariant upstairs boundary. -/
def boundaryInclusion : TopCat.of BoundaryCover ⟶ TopCat.of Glued :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

/-- The actual inclusion of the geometric boundary in the orbit bordification. -/
def boundaryBaseInclusion : TopCat.of BoundaryBase ⟶ TopCat.of BordifiedOrbit :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

/-- The actual boundary quotient projection is the restriction of the whole projection. -/
def boundaryProjection : TopCat.of BoundaryCover ⟶ TopCat.of BoundaryBase :=
  TopCat.ofHom ⟨fun x => ⟨projection principalSix x.val,(boundary_iff x.val).mp x.property⟩,
    ((projection_continuous principalSix).comp continuous_subtype_val).subtype_mk _⟩

/-- The set equality identifying the boundary with the covering preimage is a homeomorphism. -/
def boundaryPreimageHomeomorph : BoundaryCover ≃ₜ
    ((projection principalSix) ⁻¹' boundary principalSix) :=
  Homeomorph.setCongr (projection_preimage_boundary principalSix).symm

/-- Restriction of the actual covering to its boundary is still a genuine covering. -/
theorem boundaryCovering : IsCoveringMap boundaryProjection := by
  exact (wholeQuotientCovering.isCoveringMap.restrictPreimage (boundary principalSix)).comp_homeomorph
    boundaryPreimageHomeomorph

theorem boundaryProjection_surjective : Function.Surjective boundaryProjection := by
  intro y
  obtain ⟨x,hx⟩ := wholeQuotientCovering.surjective y.val
  change projection principalSix x=y.val at hx
  refine ⟨⟨x,(boundary_iff x).mpr (by rw [hx]; exact y.property)⟩,?_⟩
  exact Subtype.ext hx

/-- The actual deck action remains free on its invariant boundary. -/
instance boundaryFree : IsCancelSMul principalSix BoundaryCover :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
    intro g x hx
    exact SymmetricSpaceBordifiedPrincipalSix.principalSix_fixed_eq_one
      SymmetricSpaceGluedArithmetic.compact_transporter_finite g x.val
        (congrArg Subtype.val hx))

/-- The boundary restriction retains the literal principal-six quotient-covering structure. -/
theorem boundaryQuotientCovering : IsQuotientCoveringMap boundaryProjection principalSix := by
  apply (isQuotientCoveringMap_iff_isCoveringMap_and ..).mpr
  refine ⟨boundaryCovering,boundaryProjection_surjective,inferInstance,inferInstance,?_⟩
  intro x y
  constructor
  · intro h
    obtain ⟨g,hg⟩ := wholeQuotientCovering.apply_eq_iff_mem_orbit.mp (congrArg Subtype.val h)
    exact ⟨g,Subtype.ext hg⟩
  · rintro ⟨g,rfl⟩
    apply Subtype.ext
    exact projection_smul principalSix g y.val

/-- The literal boundary inclusion square commutes before passage to cochains. -/
theorem boundary_square :
    boundaryInclusion ≫ wholeProjection=boundaryProjection ≫ boundaryBaseInclusion := rfl

theorem boundaryInclusion_equivariant (g : principalSix) (x : BoundaryCover) :
    boundaryInclusion (g • x)=g • boundaryInclusion x := rfl

theorem boundaryInclusion_injective : Function.Injective boundaryInclusion := Subtype.val_injective

end TernaryPoly.SingularBoundaryRestriction
