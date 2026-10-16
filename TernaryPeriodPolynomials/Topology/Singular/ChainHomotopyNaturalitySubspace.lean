module

public import TernaryPeriodPolynomials.Topology.Singular.ChainHomotopyNaturalityTop
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularChainHomotopyNaturality
open CategoryTheory Limits HomologicalComplex
open RationalRelativeSingular ContractibleSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X,Y)} (S : Set X) (T : Set Y) (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T)
  (H : ContinuousMap.Homotopy f g) (hH : ∀ t x, x ∈ S → H (t,x) ∈ T)

/-- The pinned actual singular chain homotopy restricts through literal subspace inclusions to
the pinned actual chain homotopy of the genuine restricted topological homotopy, in all degrees. -/
theorem subspace_singularChainHomotopy_natural (p q : ℕ) :
    (inclusion S).f p ≫
        (TopCat.Homotopy.singularChainComplexFunctorObjMap
          (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℚ ℚ)).hom p q =
      (TopCat.Homotopy.singularChainComplexFunctorObjMap
          (f := TopCat.ofHom (subspaceMap f S T hf)) (g := TopCat.ofHom (subspaceMap g S T hg))
          (subspaceHomotopy S T hf hg H hH) (ModuleCat.of ℚ ℚ)).hom p q ≫ (inclusion T).f q :=
  singularChainHomotopy_natural
    (show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from H)
    (show TopCat.Homotopy (TopCat.ofHom (subspaceMap f S T hf))
      (TopCat.ofHom (subspaceMap g S T hg)) from subspaceHomotopy S T hf hg H hH)
    (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) (fun _ _ => rfl) (ModuleCat.of ℚ ℚ) p q

include hf hg hH in
/-- Every component of a genuine pair-preserving singular chain homotopy kills source subspace
chains after the literal target relative-chain projection. This is the exact cokernel descent condition. -/
theorem subspace_singularChainHomotopy_relative_zero (p q : ℕ) :
    (inclusion S).f p ≫
        (TopCat.Homotopy.singularChainComplexFunctorObjMap
          (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℚ ℚ)).hom p q ≫
        (cokernel.π (inclusion T)).f q = 0 := by
  rw [← Category.assoc,subspace_singularChainHomotopy_natural S T hf hg H hH,Category.assoc]
  have h := HomologicalComplex.congr_hom (cokernel.condition (inclusion T)) q
  change (inclusion T).f q ≫ (cokernel.π (inclusion T)).f q = 0 at h
  rw [h,comp_zero]

end TernaryPoly.SingularChainHomotopyNaturality
