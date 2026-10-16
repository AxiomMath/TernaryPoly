module

public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains

@[expose] public section


noncomputable section
open CategoryTheory HomologicalComplex
namespace TernaryPoly.SingularCoverNaturality
open EquivariantSingularResolution EquivariantSingularCohomology

variable {G : Type} [Group G] {E E' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x)=g • F x)
  [ContractibleSpace E] [IsCancelSMul G E]
  [ContractibleSpace E'] [IsCancelSMul G E']

/-- The chosen comparison with the bar resolution preserves the actual augmentation. -/
theorem resolutionComparison_augmentation :
    resolutionComparison G E ≫ (Rep.barResolution ℚ G).π=augmentationChain G E :=
  ProjectiveResolution.homotopyEquiv_hom_π (projectiveResolution G E) (Rep.barResolution ℚ G)

/-- Naturality of the chosen resolution comparison holds up to an actual chain homotopy. -/
def resolutionComparisonHomotopy :
    Homotopy (chainMap F hF ≫ resolutionComparison G E') (resolutionComparison G E) := by
  apply ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial ℚ G ℚ))
    (P := projectiveResolution G E) (Q := Rep.barResolution ℚ G)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => chainMap F hF ≫ m)
        (resolutionComparison_augmentation (G := G) (E := E'))).trans
          ((chainMap_augmentationChain F hF).trans
            ((Category.comp_id _).symm.trans (congrArg (fun m => augmentationChain G E ≫ m)
              ((ChainComplex.single₀ (Rep ℚ G)).map_id _).symm))))
  · exact (resolutionComparison_augmentation (G := G) (E := E)).trans
      ((Category.comp_id _).symm.trans (congrArg (fun m => augmentationChain G E ≫ m)
        ((ChainComplex.single₀ (Rep ℚ G)).map_id _).symm))

/-- Applying the contravariant Hom functor transports the actual chain homotopy. -/
def barComparisonHomotopy (V : Rep ℚ G) :
    Homotopy (barComparison G E' V ≫ cochainPullback F hF V) (barComparison G E V) := by
  let h := ((linearYoneda ℚ (Rep ℚ G)).obj V).rightOp.mapHomotopy
    (resolutionComparisonHomotopy F hF)
  exact h.unop

/-- The actual comparison with singular cohomology commutes with space pullback. -/
theorem groupCohomologyIso_pullback (V : Rep ℚ G) (n : ℕ) :
    (EquivariantSingularCohomology.groupCohomologyIso G E' V n).hom ≫
        homologyMap (cochainPullback F hF V) n=
      (EquivariantSingularCohomology.groupCohomologyIso G E V n).hom := by
  change homologyMap (comparisonMap G E' V) n ≫ homologyMap (cochainPullback F hF V) n=
    homologyMap (comparisonMap G E V) n
  simp only [comparisonMap,homologyMap_comp,Category.assoc]
  rw [←homologyMap_comp,(barComparisonHomotopy F hF V).homologyMap_eq]

end TernaryPoly.SingularCoverNaturality
