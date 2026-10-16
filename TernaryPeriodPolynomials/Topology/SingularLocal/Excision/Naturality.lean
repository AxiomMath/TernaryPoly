module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Theorem
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionPoint

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalHomology

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] [IsCancelSMul G E]

omit [IsCancelSMul G E] in
/-- Actual supported-chain inclusions compose as the literal subset maps. -/
theorem subordinateMap_comp (S T Q : Set E) (hS : InvariantSet G E S)
    (hT : InvariantSet G E T) (hQ : InvariantSet G E Q) (hST : S ⊆ T) (hTQ : T ⊆ Q) :
    subordinateMap G E S T hS hT hST ≫ subordinateMap G E T Q hT hQ hTQ =
      subordinateMap G E S Q hS hQ (hST.trans hTQ) := by
  ext n c
  rfl

/-- The geometric local-chain inclusion for nested subsets composes literally. -/
theorem nestedLocalInclusion_comp (A D F : Set B) (hAD : A ⊆ D) (hDF : D ⊆ F)
    (W : Rep.{0} ℚ G) :
    nestedLocalInclusion p A D hAD W ≫ nestedLocalInclusion p D F hDF W =
      nestedLocalInclusion p A F (hAD.trans hDF) W := by
  apply (cancel_mono (localSupportedIso p F W).hom).mp
  rw [Category.assoc, ← localSupportedIso_naturality, ← Category.assoc,
    ← localSupportedIso_naturality, Category.assoc, ← Functor.map_comp,
    subordinateMap_comp, localSupportedIso_naturality]

/-- Actual relative local chains map covariantly when the excisive neighborhood grows. -/
def neighborhoodMap (A D F : Set B) (hDF : D ⊆ F) (W : Rep.{0} ℚ G) :
    neighborhoodRelativeChains p A D W ⟶ neighborhoodRelativeChains p A F W :=
  cokernel.map _ _ (nestedLocalInclusion p (A ∩ D) (A ∩ F) (Set.inter_subset_inter_right A hDF) W)
    (nestedLocalInclusion p D F hDF W) (by
      rw [nestedLocalInclusion_comp, nestedLocalInclusion_comp])

/-- The genuine geometric pair maps commute with every inclusion of smaller neighborhoods. -/
theorem localExcisionMap_natural (A D F : Set B) (hDF : D ⊆ F) (W : Rep.{0} ℚ G) :
    neighborhoodMap p A D F hDF W ≫ localExcisionMap p A F W = localExcisionMap p A D W := by
  apply (cancel_epi (cokernel.π (nestedLocalInclusion p (A ∩ D) D Set.inter_subset_right W))).mp
  simp only [neighborhoodMap, localExcisionMap, cokernel.map, Category.assoc,
    cokernel.π_desc_assoc, cokernel.π_desc]
  rw [← Category.assoc, nestedLocalInclusion_inclusion]

/-- Actual geometric excision isomorphisms are natural under smaller excisive neighborhoods. -/
theorem localExcisionHomologyIso_natural (A D F : Opens B) (hAD : A ⊔ D = ⊤)
    (hAF : A ⊔ F = ⊤) (hDF : D ≤ F) (W : Rep.{0} ℚ G) (n : ℕ) :
    homologyMap (neighborhoodMap p (A : Set B) D F hDF W) n ≫
      (localExcisionHomologyIso p A F hAF W n).hom = (localExcisionHomologyIso p A D hAD W n).hom := by
  rw [localExcisionHomologyIso_hom, localExcisionHomologyIso_hom, ← homologyMap_comp]
  erw [localExcisionMap_natural]

/-- Actual geometric local homology at a point is computed in every open neighborhood. -/
def pointLocalExcisionHomologyIso [T1Space B] (x : B) (D : Opens B) (hx : x ∈ D)
    (W : Rep.{0} ℚ G) (n : ℕ) :
    (neighborhoodRelativeChains p ({x}ᶜ : Set B) D W).homology n ≅
      (relativeLocalChains p ({x}ᶜ : Set B) W).homology n :=
  localExcisionHomologyIso p (RationalRelativeExcision.puncturedOpen x) D
    (RationalRelativeExcision.puncturedOpen_sup x D hx) W n

/-- The point-local coefficient isomorphism is induced by the actual punctured pair inclusion. -/
theorem pointLocalExcisionHomologyIso_hom [T1Space B] (x : B) (D : Opens B) (hx : x ∈ D)
    (W : Rep.{0} ℚ G) (n : ℕ) :
    (pointLocalExcisionHomologyIso p x D hx W n).hom =
      homologyMap (localExcisionMap p ({x}ᶜ : Set B) D W) n := rfl

/-- Point-local coefficient excision is natural under actual inclusions of smaller neighborhoods. -/
theorem pointLocalExcisionHomologyIso_natural [T1Space B] (x : B) (D F : Opens B)
    (hxD : x ∈ D) (hxF : x ∈ F) (hDF : D ≤ F) (W : Rep.{0} ℚ G) (n : ℕ) :
    homologyMap (neighborhoodMap p ({x}ᶜ : Set B) D F hDF W) n ≫
      (pointLocalExcisionHomologyIso p x F hxF W n).hom =
        (pointLocalExcisionHomologyIso p x D hxD W n).hom := by
  rw [pointLocalExcisionHomologyIso_hom, pointLocalExcisionHomologyIso_hom, ← homologyMap_comp]
  erw [localExcisionMap_natural]

end TernaryPoly.SingularLocalExcision
