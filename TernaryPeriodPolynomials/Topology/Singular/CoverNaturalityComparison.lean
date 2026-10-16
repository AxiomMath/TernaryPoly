module

public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityCochains
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityHomotopy

@[expose] public section


noncomputable section
open CategoryTheory HomologicalComplex
namespace TernaryPoly.SingularCoverNaturality
open SingularLocalCoefficient

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p'=p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x)=g • F x)
  [ContractibleSpace E] [IsCancelSMul G E]
  [ContractibleSpace E'] [IsCancelSMul G E']

/-- The genuine group-to-local-system cohomology comparison is natural under equivariant cover maps. -/
theorem groupLocalCohomologyIso_pullback (V : Rep ℚ G) (n : ℕ) :
    (groupLocalCohomologyIso p' hp' V n).hom ≫
        homologyMap (localPullback p p' F f hsquare hp hp' hF V) n=
      (groupLocalCohomologyIso p hp V n).hom := by
  change ((EquivariantSingularCohomology.groupCohomologyIso G E' V n).hom ≫
      homologyMap (cochainIso p' hp' V).hom n) ≫
      homologyMap (localPullback p p' F f hsquare hp hp' hF V) n=
    (EquivariantSingularCohomology.groupCohomologyIso G E V n).hom ≫
      homologyMap (cochainIso p hp V).hom n
  rw [Category.assoc,←homologyMap_comp,←cochainIso_pullback,homologyMap_comp,
    ←Category.assoc,groupCohomologyIso_pullback]

/-- The pullback associated with an equivariant map between contractible free covers is an isomorphism. -/
instance localPullback_homology_isIso (V : Rep ℚ G) (n : ℕ) :
    IsIso (homologyMap (localPullback p p' F f hsquare hp hp' hF V) n) := by
  have h := groupLocalCohomologyIso_pullback p p' F f hsquare hp hp' hF V n
  have heq : homologyMap (localPullback p p' F f hsquare hp hp' hF V) n=
      (groupLocalCohomologyIso p' hp' V n).inv ≫ (groupLocalCohomologyIso p hp V n).hom := by
    rw [←h,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  rw [heq]
  infer_instance

end TernaryPoly.SingularCoverNaturality
