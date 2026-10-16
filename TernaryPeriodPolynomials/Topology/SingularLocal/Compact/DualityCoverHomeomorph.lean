module

public import TernaryPeriodPolynomials.Topology.Singular.CoverPullbackIso
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceChains
public import TernaryPeriodPolynomials.Topology.SingularLocal.NestedRestriction

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory HomologicalComplex
open SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality SingularLocalSupport
open EquivariantSingularSmall
variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B')

/-- An actual equivariant homeomorphism square of covering spaces. -/
structure CoverHomeomorph where
  total : E ≃ₜ E'
  base : B ≃ₜ B'
  square : (TopCat.isoOfHomeo total).hom ≫ p' = p ≫ (TopCat.isoOfHomeo base).hom
  equivariant : ∀ (g : G) (x : E), total (g • x) = g • total x

variable {p p'}

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
/-- The covering square commutes on actual points. -/
theorem CoverHomeomorph.square_apply (h : CoverHomeomorph (G := G) p p') (x : E) :
    p' (h.total x) = h.base (p x) := congrArg (fun f => f x) h.square

/-- The actual inverse square is again an equivariant covering homeomorphism. -/
def CoverHomeomorph.symm (h : CoverHomeomorph (G := G) p p') : CoverHomeomorph (G := G) p' p where
  total := h.total.symm
  base := h.base.symm
  square := by
    ext x
    apply h.base.injective
    exact (h.square_apply (h.total.symm x)).symm.trans (by simp)
  equivariant g x := by
    apply h.total.injective
    rw [h.total.apply_symm_apply,h.equivariant,h.total.apply_symm_apply]

variable [hp : Fact (IsQuotientCoveringMap p G)] [hp' : Fact (IsQuotientCoveringMap p' G)]
  (h : CoverHomeomorph (G := G) p p') (V : Rep.{0} ℚ G)

/-- The actual geometric cochain pullback of the covering homeomorphism square. -/
def coveringCochainMap : localCochains p' hp'.out V ⟶ localCochains p hp.out V :=
  localPullback p p' (TopCat.isoOfHomeo h.total).hom (TopCat.isoOfHomeo h.base).hom h.square
    hp.out hp'.out h.equivariant V

/-- Genuine homeomorphism pullback is an isomorphism on actual local cochains. -/
theorem coveringCochainMap_isIso : IsIso (coveringCochainMap h V) := by
  have := cochainPullback_isIso_of_inverse (TopCat.isoOfHomeo h.total).hom
    (TopCat.isoOfHomeo h.total).inv h.equivariant h.symm.equivariant
    (TopCat.isoOfHomeo h.total).hom_inv_id (TopCat.isoOfHomeo h.total).inv_hom_id V
  unfold coveringCochainMap
  apply localPullback_isIso

/-- The actual covering homeomorphism restricts to every base subset and its preimage. -/
def CoverHomeomorph.restrict (S : Set B') :
    CoverHomeomorph (G := G) (restrictedProjection p (h.base ⁻¹' S)) (restrictedProjection p' S) where
  total := h.total.subtype (fun x => by
    change h.base (p x) ∈ S ↔ p' (h.total x) ∈ S
    rw [h.square_apply])
  base := h.base.subtype (fun _ => Iff.rfl)
  square := by
    ext x
    exact h.square_apply x.val
  equivariant g x := Subtype.ext (h.equivariant g x.val)

/-- Literal geometric pullback commutes with actual restriction to a base subset. -/
theorem coveringCochainMap_restriction (S : Set B') :
    coveringCochainMap h V ≫ localRestriction p (h.base ⁻¹' S) V =
      localRestriction p' S V ≫ coveringCochainMap (h.restrict S) V := by
  unfold coveringCochainMap localRestriction
  erw [← localPullback_comp]

end TernaryPoly.SingularLocalCompactDuality
