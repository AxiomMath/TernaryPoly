module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameFunctions

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits
open FreeActionLinearization
open scoped Simplicial
variable (X : TopCat.{0}) (F : ModuleCat.{0} ℝ) (n : ℕ)

/-- Evaluate an actual real singular linear cochain at the actual coefficient-one simplex generator. -/
def ordinaryCochainEvaluation :
    ((SmoothSingularComparison.realSingularChains X).X n →ₗ[ℝ] F) →ₗ[ℝ] (SingularSimplex X n → F) where
  toFun φ σ := φ (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ) 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual real singular cochains are determined by their literal coefficient-one generator values. -/
theorem ordinaryCochainEvaluation_injective : Function.Injective (ordinaryCochainEvaluation X F n) := by
  intro φ ψ h
  have he : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro σ
    ext
    exact congrFun h σ
  exact congrArg ModuleCat.Hom.hom he

/-- Any coefficient-valued simplex function extends to an actual real singular linear cochain. -/
theorem ordinaryCochainEvaluation_surjective : Function.Surjective (ordinaryCochainEvaluation X F n) := by
  intro c
  let φ : (SmoothSingularComparison.realSingularChains X).X n ⟶ F :=
    Sigma.desc (fun σ : SingularSimplex X n => ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ F (c σ)))
  refine ⟨φ.hom, ?_⟩
  funext σ
  have h : (TopCat.toSSet.obj X).ιChainComplex σ ≫ φ =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ F (c σ)) := Sigma.ι_comp_desc _ _
  exact (congrArg (fun m => m.hom 1) h).trans (one_smul ℝ (c σ))

/-- The literal ordinary simplex-value identification for the actual real singular Hom complex. -/
def ordinaryFunctionEquiv :
    ((SmoothSingularComparison.realSingularChains X).X n →ₗ[ℝ] F) ≃ₗ[ℝ] (SingularSimplex X n → F) :=
  LinearEquiv.ofBijective (ordinaryCochainEvaluation X F n)
    ⟨ordinaryCochainEvaluation_injective X F n, ordinaryCochainEvaluation_surjective X F n⟩

/-- The ordinary simplex identification evaluates the literal actual generator. -/
theorem ordinaryFunctionEquiv_apply
    (φ : (SmoothSingularComparison.realSingularChains X).X n →ₗ[ℝ] F)
    (σ : SingularSimplex X n) :
    ordinaryFunctionEquiv X F n φ σ =
      φ (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ) 1) := rfl

end TernaryPoly.SmoothSingularGlobal
