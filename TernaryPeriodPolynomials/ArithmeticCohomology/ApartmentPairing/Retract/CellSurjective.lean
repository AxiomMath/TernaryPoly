module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellResolution

@[expose] public section


/-!
# The cellular classes surject onto (indeed are isomorphic to) the group homology of `Γ(6)`

The cellular chain map `cellChainMap` is compatible with the augmentations of the two projective
resolutions of the trivial representation (`cellResolution` and the singular chains of the contractible
bordification, `projectiveResolution`), hence homotopic to the comparison map of the two resolutions
(`liftHomotopy`).  Applying the additive functor `(Rep.coinvariantsTensor ℚ Γ(6)).obj W` preserves homotopies,
so `cellCoinvMap W` induces isomorphisms in homology (`cellCoinvMap_isIso`), and so does
`cellGroupHomologyMap W n` (`cellGroupHomologyMap_isIso`), in particular
`cellGroupHomologyMap_surjective`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open CategoryTheory Finsupp GeneralEisenstein TernaryPoly TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularLocalHomology TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing
  TernaryPoly.FreeActionLinearization

theorem augmentationModule_sing (σ : SingularSimplex (TopCat.of Glued) 0) :
    (augmentationModule (TopCat.of Glued)).hom
      (TernaryPeriodPolynomials.Argument.Lemma33.sing (TopCat.of Glued) σ) = 1 := by
  have h := congrArg (fun f => f.hom (1 : ℚ)) (generator_augmentation (TopCat.of Glued) σ)
  exact h

theorem cellAt_aug (C : Cell) : (augmentationModule (TopCat.of Glued)).hom (cellAt 0 C) = epsQ C := by
  rw [cellAt_zero, map_smul, augmentationModule_sing, smul_eq_mul, mul_one]

theorem cellChainF_aug : cellChainF 0 ≫ augmentation principalSix (TopCat.of Glued) = cellAug0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change (augmentationModule (TopCat.of Glued)).hom ((cellChainF 0).hom z) = cellAug0.hom z
  rw [cellChainF_hom, cellAug0_hom]
  have key : (augmentationModule (TopCat.of Glued)).hom ∘ₗ
      linearCombination ℚ (fun C : Graded 0 => cellAt 0 C.1) = augQ := by
    apply Finsupp.lhom_ext
    intro C a
    have e : (single C a : Graded 0 →₀ ℚ) = a • single C 1 := by simp
    rw [e, map_smul, map_smul]
    simp only [LinearMap.comp_apply, linearCombination_single, one_smul, augQ_single]
    rw [cellAt_aug]
  exact LinearMap.congr_fun key _

/-- The cellular chain map is compatible with the augmentations. -/
theorem cellChainMap_aug :
    cellChainMap ≫ augmentationChain principalSix (TopCat.of Glued) = cellAug := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
    rw [HomologicalComplex.comp_f, augmentationChain_f_zero]
    exact cellChainF_aug
  | succ i =>
    exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero i)).eq_of_tgt _ _

/-- The cellular chain map is homotopic to the comparison map of the two projective resolutions. -/
def cellChainHomotopy : Homotopy cellChainMap
    (ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ principalSix ℚ)) cellResolution
      (projectiveResolution principalSix (TopCat.of Glued))) :=
  ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial ℚ principalSix ℚ))
    (P := cellResolution) (Q := projectiveResolution principalSix (TopCat.of Glued)) _ _
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact cellChainMap_aug)
    (ProjectiveResolution.lift_commutes _ _ _)

/-- With coefficients in any `W`, the cellular chain map induces isomorphisms in homology. -/
instance cellCoinvMap_isIso (W : Rep.{0} ℚ principalSix) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cellCoinvMap W) n) := by
  let F := (Rep.coinvariantsTensor ℚ principalSix).obj W
  let hE := F.mapHomotopyEquiv
    (cellResolution.homotopyEquiv (projectiveResolution principalSix (TopCat.of Glued)))
  have h : HomologicalComplex.homologyMap (cellCoinvMap W) n =
      HomologicalComplex.homologyMap hE.hom n :=
    (F.mapHomotopy cellChainHomotopy).homologyMap_eq n
  rw [h]
  exact inferInstanceAs (IsIso (hE.toHomologyIso n).hom)

instance cellGroupHomologyMap_isIso (W : Rep.{0} ℚ principalSix) (n : ℕ) :
    IsIso (cellGroupHomologyMap W n) := by
  unfold cellGroupHomologyMap cellToBordified
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

theorem cellGroupHomologyMap_surjective (W : Rep.{0} ℚ principalSix) :
    Function.Surjective (cellGroupHomologyMap W 3).hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
