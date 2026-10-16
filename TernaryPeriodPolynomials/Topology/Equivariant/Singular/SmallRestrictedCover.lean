module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallSubspaceNaturality
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityCochains

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularSmall
open CategoryTheory HomologicalComplex EquivariantSingularResolution SingularCoverNaturality
open SphereOddDegree SingularLocalCoefficient

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (A : Set B)

omit [ContinuousConstSMul G E] in
/-- The literal preimage of every base subset is invariant under the actual deck action. -/
theorem preimage_invariant : InvariantSet G E (p ⁻¹' A) := by
  intro g x hx
  change p (g • x) ∈ A
  rw [hp.out.map_smul]
  exact hx

instance preimageInvariantFact : Fact (InvariantSet G E (p ⁻¹' A)) := ⟨preimage_invariant p A⟩

/-- Restriction of the actual quotient covering to the literal preimage of a base subset. -/
def restrictedProjection : TopCat.of (p ⁻¹' A) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨A.restrictPreimage p,(p.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The restricted projection is an actual quotient covering with the canonical restricted action. -/
theorem restrictedQuotientCovering : IsQuotientCoveringMap (restrictedProjection p A) G := by
  apply (isQuotientCoveringMap_iff_isCoveringMap_and ..).mpr
  have : IsCancelSMul G E := hp.out.isCancelSMul
  refine ⟨hp.out.isCoveringMap.restrictPreimage A,?_,inferInstance,inferInstance,?_⟩
  · intro y
    obtain ⟨x,hx⟩ := hp.out.surjective y.val
    exact ⟨⟨x,by change p x ∈ A; rw [hx]; exact y.property⟩,Subtype.ext hx⟩
  · intro x y
    constructor
    · intro h
      obtain ⟨g,hg⟩ := hp.out.apply_eq_iff_mem_orbit.mp (congrArg Subtype.val h)
      exact ⟨g,Subtype.ext hg⟩
    · rintro ⟨g,rfl⟩
      exact Subtype.ext (hp.out.map_smul g)

/-- The actual restricted projection forms the literal inclusion square. -/
theorem restricted_square :
    sInclusion (p ⁻¹' A) ≫ p = restrictedProjection p A ≫ sInclusion A := rfl

/-- The actual geometric local-system restriction to a base subset. -/
def localRestriction (W : Rep.{0} ℚ G) :
    localCochains p hp.out W ⟶ localCochains (restrictedProjection p A) (restrictedQuotientCovering p A) W :=
  localPullback (restrictedProjection p A) p (sInclusion (p ⁻¹' A)) (sInclusion A)
    (restricted_square p A) (restrictedQuotientCovering p A) hp.out (fun _ _ => rfl) W

/-- The actual subordinate-chain Hom cochains identify with genuine restricted local cochains. -/
def subordinateLocalIso (W : Rep.{0} ℚ G) :
    homCochains (subordinateComplex G E (p ⁻¹' A) (preimage_invariant p A)) W ≅
      localCochains (restrictedProjection p A) (restrictedQuotientCovering p A) W :=
  subspaceCochainIso G E (p ⁻¹' A) (preimage_invariant p A) (fun _ _ => rfl) W ≪≫
    cochainIso (restrictedProjection p A) (restrictedQuotientCovering p A) W

/-- Ambient subordinate restriction is precisely the genuine geometric local-system restriction. -/
theorem subordinateLocalIso_restriction (W : Rep.{0} ℚ G) :
    homPullback (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)) W ≫
      (subordinateLocalIso p A W).hom = (cochainIso p hp.out W).hom ≫ localRestriction p A W := by
  rw [subordinateLocalIso, Iso.trans_hom, ← Category.assoc, subspaceCochainIso_inclusion]
  exact cochainIso_pullback (restrictedProjection p A) p (sInclusion (p ⁻¹' A)) (sInclusion A)
    (restricted_square p A) (restrictedQuotientCovering p A) hp.out (fun _ _ => rfl) W

end TernaryPoly.EquivariantSingularSmall
