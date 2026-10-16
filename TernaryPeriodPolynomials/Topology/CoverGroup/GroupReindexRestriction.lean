module

public import TernaryPeriodPolynomials.Topology.CoverGroup.GroupReindexCochains
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallRestrictedCover

@[expose] public section


/-! Group reindexing preserves actual geometric restriction to every base subset. -/
noncomputable section
namespace TernaryPoly.CoverGroupReindex
open CategoryTheory HomologicalComplex EquivariantSingularSmall SingularLocalCoefficient

variable {G H : Type} [Group G] [Group H] (e : H ≃* G)
  {E B : TopCat.{0}} [MulAction H E] [MulAction G E]
  [ContinuousConstSMul H E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hH : Fact (IsQuotientCoveringMap p H)] [hG : Fact (IsQuotientCoveringMap p G)]
  (hact : ∀ (h : H) (x : E), h • x = e h • x) (V : Rep.{0} ℚ G)

include hact in
omit [ContinuousConstSMul H E] [ContinuousConstSMul G E] in
theorem restricted_action (A : Set B) (h : H) (x : TopCat.of (p ⁻¹' A)) :
    h • x = e h • x := Subtype.ext (hact h x.val)

def restrictedCochainIso (A : Set B) :
    localCochains (restrictedProjection p A) (restrictedQuotientCovering (G := G) p A) V ≅
      localCochains (restrictedProjection p A) (restrictedQuotientCovering (G := H) p A)
        (Rep.res e.toMonoidHom V) :=
  cochainIso e (restrictedProjection p A) (restrictedQuotientCovering (G := H) p A)
    (restrictedQuotientCovering (G := G) p A) (restricted_action e p hact A) V

theorem cochainIso_restriction (A : Set B) :
    (cochainIso e p hH.out hG.out hact V).hom ≫ localRestriction p A (Rep.res e.toMonoidHom V) =
      localRestriction p A V ≫ (restrictedCochainIso e p hact V A).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext σ
  apply Subtype.ext
  rfl

end TernaryPoly.CoverGroupReindex
