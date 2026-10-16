module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceChains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory HomologicalComplex EquivariantSingularResolution
open scoped Classical

variable {G : Type} [Group G] {E E' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
  [ContractibleSpace E] [IsCancelSMul G E]
  [ContractibleSpace E'] [IsCancelSMul G E']

/-- The actual bar-to-singular comparison is augmentation-compatible. -/
theorem resolutionInverse_augmentation :
    (resolutionHomotopyEquiv G E).inv ≫ augmentationChain G E = (Rep.barResolution ℚ G).π :=
  ProjectiveResolution.homotopyEquiv_inv_π (projectiveResolution G E) (Rep.barResolution ℚ G)

/-- Two literal augmentation-preserving maps from the bar resolution are homotopic. -/
def resolutionInverse_space_homotopy :
    Homotopy ((resolutionHomotopyEquiv G E).inv ≫ SingularCoverNaturality.chainMap F hF)
      (resolutionHomotopyEquiv G E').inv := by
  apply ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial ℚ G ℚ))
    (P := Rep.barResolution ℚ G) (Q := projectiveResolution G E')
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => (resolutionHomotopyEquiv G E).inv ≫ m)
        (SingularCoverNaturality.chainMap_augmentationChain F hF)).trans
          ((resolutionInverse_augmentation (G := G) (E := E)).trans
            ((Category.comp_id _).symm.trans (congrArg (fun m => (Rep.barResolution ℚ G).π ≫ m)
              ((ChainComplex.single₀ (Rep ℚ G)).map_id _).symm))))
  · exact (resolutionInverse_augmentation (G := G) (E := E')).trans
      ((Category.comp_id _).symm.trans (congrArg (fun m => (Rep.barResolution ℚ G).π ≫ m)
        ((ChainComplex.single₀ (Rep ℚ G)).map_id _).symm))

/-- Actual coinvariants preserve the space-naturality comparison homotopy. -/
def coinvariantInverse_space_homotopy (V : Rep.{0} ℚ G) :
    Homotopy ((coinvariantResolutionHomotopyEquiv G E V).inv ≫ coinvariantSpaceMap F hF V)
      (coinvariantResolutionHomotopyEquiv G E' V).inv := by
  let T := ((Rep.coinvariantsTensor ℚ G).obj V).mapHomologicalComplex (ComplexShape.down ℕ)
  change Homotopy (T.map (resolutionHomotopyEquiv G E).inv ≫
    T.map (SingularCoverNaturality.chainMap F hF)) (T.map (resolutionHomotopyEquiv G E').inv)
  rw [← T.map_comp]
  exact ((Rep.coinvariantsTensor ℚ G).obj V).mapHomotopy (resolutionInverse_space_homotopy F hF)

/-- The concrete homology comparison commutes with the actual covariant singular map. -/
theorem groupCoinvariantHomologyIso_space_natural (V : Rep.{0} ℚ G) (n : ℕ) :
    (groupCoinvariantHomologyIso G E V n).hom ≫ homologyMap (coinvariantSpaceMap F hF V) n =
      (groupCoinvariantHomologyIso G E' V n).hom := by
  change homologyMap (comparisonMap G E V) n ≫ homologyMap (coinvariantSpaceMap F hF V) n =
    homologyMap (comparisonMap G E' V) n
  simp only [comparisonMap, homologyMap_comp, Category.assoc]
  rw [← homologyMap_comp, (coinvariantInverse_space_homotopy F hF V).homologyMap_eq]

variable {B B' : TopCat.{0}} (p : E ⟶ B) (p' : E' ⟶ B')
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)

/-- The actual geometric homology comparison is covariantly natural in maps of free contractible covers. -/
theorem groupLocalHomologyIso_space_natural (V : Rep.{0} ℚ G) (n : ℕ) :
    (groupLocalHomologyIso p hp V n).hom ≫ homologyMap (localSpaceMap F hF V p p' hp hp') n =
      (groupLocalHomologyIso p' hp' V n).hom := by
  have h := congrArg (fun m => homologyMap m n) (chainIso_space_natural F hF V p p' hp hp')
  simp only [homologyMap_comp] at h
  change ((groupCoinvariantHomologyIso G E V n).hom ≫ homologyMap (chainIso p hp V).hom n) ≫ _ =
    (groupCoinvariantHomologyIso G E' V n).hom ≫ homologyMap (chainIso p' hp' V).hom n
  rw [Category.assoc, h, ← Category.assoc, groupCoinvariantHomologyIso_space_natural]

/-- Such a geometric map induces an isomorphism on local-coefficient homology in every degree. -/
instance localSpaceMap_homology_isIso (V : Rep.{0} ℚ G) (n : ℕ) :
    IsIso (homologyMap (localSpaceMap F hF V p p' hp hp') n) := by
  have h := groupLocalHomologyIso_space_natural F hF p p' hp hp' V n
  have : IsIso ((groupLocalHomologyIso p hp V n).hom ≫
      homologyMap (localSpaceMap F hF V p p' hp hp') n) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (groupLocalHomologyIso p hp V n).hom
    (homologyMap (localSpaceMap F hF V p p' hp hp') n)

end TernaryPoly.SingularLocalHomology
