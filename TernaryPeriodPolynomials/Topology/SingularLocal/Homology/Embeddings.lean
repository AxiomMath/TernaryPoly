module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceChains
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionSurjective

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory FreeActionLinearization CoveringSingularOrbits
open scoped Classical

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E'] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)
  (hinj : Function.Injective f)

/-- The graded retraction to the actual image simplices of an injective base map, with actual fiber pullback. -/
def gradedSpaceRetraction (n : ℕ) : VertexChain p' hp' V n →ₗ[ℚ] VertexChain p hp V n :=
  (DFinsupp.mapRange.linearMap (fun σ : SingularSimplex B n =>
    (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ)).symm.toLinearMap)).comp
    (show VertexChain p' hp' V n →ₗ[ℚ]
      (Π₀ σ : SingularSimplex B n, FiberCoefficient p' hp' V (f (atVertex σ))) from
    { toFun := DFinsupp.comapDomain (projection f n) (SingularBoundaryRestriction.simplexMap_injective f hinj n)
      map_add' c d := DFinsupp.comapDomain_add _ _ c d
      map_smul' r c := DFinsupp.comapDomain_smul _ _ r c })

omit [ContinuousConstSMul G E] [IsCancelSMul G E] [ContinuousConstSMul G E'] [IsCancelSMul G E'] in
/-- The graded retraction recovers every elementary chain in the actual image. -/
theorem gradedSpaceRetraction_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    gradedSpaceRetraction p p' F f hsquare hp hp' hF V hinj n
      (DFinsupp.single (projection f n σ)
        (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ) c)) =
      DFinsupp.single σ c := by
  let L := DFinsupp.mapRange.linearMap (fun σ : SingularSimplex B n =>
    (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ)).symm.toLinearMap)
  have h := DFinsupp.comapDomain_single
    (β := fun σ : SingularSimplex B' n => FiberCoefficient p' hp' V (atVertex σ))
    (projection f n) (SingularBoundaryRestriction.simplexMap_injective f hinj n) σ
    (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ) c)
  apply (congrArg L h).trans
  apply DFinsupp.ext
  intro τ
  change (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex τ)).symm
    ((DFinsupp.single σ (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ) c) :
      Π₀ σ : SingularSimplex B n, FiberCoefficient p' hp' V (f (atVertex σ))) τ) =
    (DFinsupp.single σ c : VertexChain p hp V n) τ
  by_cases hτσ : τ = σ
  · subst τ
    simp
  · simp [Ne.symm hτσ]

/-- The literal map of local chains along an injective base has a degreewise linear left inverse. -/
theorem gradedSpaceRetraction_comp (n : ℕ) :
    (gradedSpaceRetraction p p' F f hsquare hp hp' hF V hinj n).comp
      ((localSpaceMap F hF V p p' hp hp').f n).hom = LinearMap.id := by
  apply DFinsupp.lhom_ext
  intro σ c
  change gradedSpaceRetraction p p' F f hsquare hp hp' hF V hinj n
    ((localSpaceMap F hF V p p' hp hp').f n (DFinsupp.single σ c)) = DFinsupp.single σ c
  rw [localSpaceMap_single F hF V p p' f hsquare hp hp']
  exact gradedSpaceRetraction_single p p' F f hsquare hp hp' hF V hinj n σ c

include hsquare hinj in
/-- Injective base maps induce injective genuine local-chain maps in each degree. -/
theorem localSpaceMap_injective (n : ℕ) :
    Function.Injective ((localSpaceMap F hF V p p' hp hp').f n) := by
  apply Function.LeftInverse.injective (g := gradedSpaceRetraction p p' F f hsquare hp hp' hF V hinj n)
  intro c
  exact LinearMap.congr_fun (gradedSpaceRetraction_comp p p' F f hsquare hp hp' hF V hinj n) c

end TernaryPoly.SingularLocalHomology
