module

public import TernaryPeriodPolynomials.Topology.SingularLocal.DualityComplex
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceChains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalDuality
open CategoryTheory HomologicalComplex FreeActionLinearization CoveringSingularOrbits
open SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality
open scoped Classical

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E'] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

/-- Actual geometric pullback and pushforward are adjoint on the nose, with the full-dual
coefficient pairing at each genuine vertex fiber. -/
theorem degreeDuality_space_natural (n : ℕ)
    (φ : VertexCochain p' hp' (dualRepresentation V) n) :
    degreeDuality p hp V n (vertexPullback p p' F f hsquare hp hp' hF (dualRepresentation V) n φ) =
      (degreeDuality p' hp' V n φ).comp ((localSpaceMap F hF V p p' hp hp').f n).hom := by
  apply DFinsupp.lhom_ext
  intro σ c
  let e := chosenFiberPoint p hp (atVertex σ)
  change degreeDuality p hp V n
      (vertexPullback p p' F f hsquare hp hp' hF (dualRepresentation V) n φ) (DFinsupp.single σ c) =
    degreeDuality p' hp' V n φ ((localSpaceMap F hF V p p' hp hp').f n (DFinsupp.single σ c))
  rw [localSpaceMap_single F hF V p p' f hsquare hp hp',
    degreeDuality_single_at p hp V n _ σ c e]
  refine Eq.trans ?_ (degreeDuality_single_at p' hp' V n φ (projection f n σ)
    (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ) c)
    (fiberMap p p' F f hsquare e)).symm
  exact (congrArg (dualValue ((φ (projection f n σ)).val (fiberMap p p' F f hsquare e)))
    (coefficientPushforward_apply p p' F f hsquare hp hp' hF V (atVertex σ) c e)).symm

/-- The actual local-system cochain duality commutes with every equivariant map of covers. -/
theorem cochainDuality_natural :
    localPullback p p' F f hsquare hp hp' hF (dualRepresentation V) ≫
        (cochainDuality p hp V).hom =
      (cochainDuality p' hp' V).hom ≫
        RationalHomologyDual.dualMap (localSpaceMap F hF V p p' hp hp') := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact degreeDuality_space_natural p p' F f hsquare hp hp' hF V n φ

/-- Naturality of the actual local-system universal-coefficient isomorphism. -/
theorem universalCoefficientIso_natural (n : ℕ) :
    homologyMap (localPullback p p' F f hsquare hp hp' hF (dualRepresentation V)) n ≫
        (universalCoefficientIso p hp V n).hom =
      (universalCoefficientIso p' hp' V n).hom ≫
        ModuleCat.ofHom (homologyMap (localSpaceMap F hF V p p' hp hp') n).hom.dualMap := by
  have h := congrArg (fun a => homologyMap a n)
    (cochainDuality_natural p p' F f hsquare hp hp' hF V)
  simp only [homologyMap_comp] at h
  change homologyMap (localPullback p p' F f hsquare hp hp' hF (dualRepresentation V)) n ≫
      (homologyMap (cochainDuality p hp V).hom n ≫
        (RationalHomologyDual.universalCoefficientIso (localChains p hp V) n).hom) =
    (homologyMap (cochainDuality p' hp' V).hom n ≫
        (RationalHomologyDual.universalCoefficientIso (localChains p' hp' V) n).hom) ≫ _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun a => a ≫
    (RationalHomologyDual.universalCoefficientIso (localChains p hp V) n).hom) h) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun a => homologyMap (cochainDuality p' hp' V).hom n ≫ a)
    (RationalHomologyDual.universalCoefficientIso_natural (localSpaceMap F hF V p p' hp hp') n)) ?_
  exact (Category.assoc _ _ _).symm

end TernaryPoly.SingularLocalDuality
