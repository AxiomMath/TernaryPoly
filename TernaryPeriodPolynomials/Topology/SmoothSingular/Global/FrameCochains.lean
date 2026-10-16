module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.OrdinaryFunctions

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits
open scoped Simplicial
variable {G : Type} [Group G] {X Y : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X] (T : SingularFrame G X Y) (V : Rep ℝ G)

/-- The actual local-frame cochain map restricts genuine Hom cochains along the actual selected lift. -/
def frameCochainRestriction : cochains G X V ⟶
    SmoothSingularComparison.realSingularCochains Y (ModuleCat.of ℝ V) where
  f n := ModuleCat.ofHom
    { toFun φ := φ.hom.toLinearMap.comp ((SmoothSingularComparison.realSingularChainMap T.lift).f n).hom
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  comm' i j h := by
    change i+1=j at h
    subst j
    rw [SmoothSingularComparison.realHom_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change φ.hom (((SmoothSingularComparison.realSingularChainMap T.lift).f i)
      ((SmoothSingularComparison.realSingularChains Y).d (i+1) i c)) =
      φ.hom ((SmoothSingularComparison.realSingularChains X).d (i+1) i
        (((SmoothSingularComparison.realSingularChainMap T.lift).f (i+1)) c))
    exact congrArg (fun m => φ.hom (m.hom c))
      ((SmoothSingularComparison.realSingularChainMap T.lift).comm (i+1) i).symm

/-- The actual cochain restriction evaluates on the literal chosen lift of each singular simplex. -/
theorem frameCochainRestriction_evaluate (n : ℕ) (φ : chainRep G X n ⟶ V)
    (σ : SingularSimplex Y n) :
    ordinaryFunctionEquiv Y (ModuleCat.of ℝ V) n ((frameCochainRestriction T V).f n φ) σ =
      cochainFunctionEquiv G X V n φ (projection T.lift n σ) := by
  exact congrArg (fun m => φ.hom (m.hom 1)) (singularGenerator_map T.lift n σ)

/-- The actual inverse of frame restriction on cochains, obtained from the actual simplex generator bases. -/
def frameCochainEquiv (n : ℕ) : (chainRep G X n ⟶ V) ≃ₗ[ℝ]
    ((SmoothSingularComparison.realSingularChains Y).X n →ₗ[ℝ] V) :=
  ((cochainFunctionEquiv G X V n).trans (frameFunctionEquiv T V n)).trans
    (ordinaryFunctionEquiv Y (ModuleCat.of ℝ V) n).symm

/-- The explicit frame equivalence agrees with the actual chain-level restriction. -/
theorem frameCochainEquiv_eq (n : ℕ) (φ : chainRep G X n ⟶ V) :
    frameCochainEquiv T V n φ = (frameCochainRestriction T V).f n φ := by
  apply (ordinaryFunctionEquiv Y (ModuleCat.of ℝ V) n).injective
  funext σ
  change ordinaryFunctionEquiv Y (ModuleCat.of ℝ V) n
    ((ordinaryFunctionEquiv Y (ModuleCat.of ℝ V) n).symm
      (frameFunctionEquiv T V n (cochainFunctionEquiv G X V n φ))) σ = _
  rw [LinearEquiv.apply_symm_apply]
  exact (frameCochainRestriction_evaluate T V n φ σ).symm

/-- Each actual degree component of local-frame restriction is invertible. -/
instance frameCochainRestriction_f_isIso (n : ℕ) : IsIso ((frameCochainRestriction T V).f n) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro φ ψ h
    exact (frameCochainEquiv T V n).injective
      ((frameCochainEquiv_eq T V n φ).trans (h.trans (frameCochainEquiv_eq T V n ψ).symm))
  · intro c
    refine ⟨(frameCochainEquiv T V n).symm c, ?_⟩
    exact (frameCochainEquiv_eq T V n _).symm.trans
      ((frameCochainEquiv T V n).apply_symm_apply c)

/-- The genuine local frame cochain map is an isomorphism of actual singular complexes. -/
instance frameCochainRestriction_isIso : IsIso (frameCochainRestriction T V) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- The actual equivariant real singular Hom complex is the ordinary real singular complex
in a genuine covering frame, with its literal chosen-lift restriction as forward map. -/
def frameSingularIso : cochains G X V ≅
    SmoothSingularComparison.realSingularCochains Y (ModuleCat.of ℝ V) :=
  asIso (frameCochainRestriction T V)

end TernaryPoly.SmoothSingularGlobal
