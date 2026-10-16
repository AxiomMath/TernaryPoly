module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Functions
public import Mathlib.CategoryTheory.Abelian.Ext

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial
namespace TernaryPoly.SmoothSingularGlobal
open FreeActionLinearization

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]

/-- The actual Hom cochain complex of the equivariant singular chain complex. -/
abbrev cochains (V : Rep ℝ G) : CochainComplex (ModuleCat ℝ) ℕ :=
  (equivariantChains G X).linearYonedaObj ℝ V

/-- The actual Hom differential is precomposition by the actual singular boundary. -/
theorem cochains_d_apply (V : Rep ℝ G) (i j : ℕ) (f : chainRep G X i ⟶ V) :
    (cochains G X V).d i j f=equivariantD G X j i ≫ f := rfl

/-- A coefficient morphism acts by literal postcomposition on the actual Hom cochains. -/
def cochainMap {V W : Rep ℝ G} (φ : V ⟶ W) : cochains G X V ⟶ cochains G X W where
  f n := ModuleCat.ofHom
    { toFun f := f ≫ φ
      map_add' f h := by simp only [Preadditive.add_comp]
      map_smul' r f := by simp only [Linear.smul_comp, RingHom.id_apply] }
  comm' i j _ := by ext f; rfl

@[simp] theorem cochainMap_apply {V W : Rep ℝ G} (φ : V ⟶ W) (n : ℕ)
    (f : chainRep G X n ⟶ V) : (cochainMap G X φ).f n f=f ≫ φ := rfl

@[simp] theorem cochainMap_id (V : Rep ℝ G) : cochainMap G X (𝟙 V)=𝟙 (cochains G X V) := by
  ext n f
  rfl

@[simp] theorem cochainMap_comp {V W U : Rep ℝ G} (φ : V ⟶ W) (ψ : W ⟶ U) :
    cochainMap G X (φ ≫ ψ)=cochainMap G X φ ≫ cochainMap G X ψ := by
  ext n f
  rfl

/-- Actual singular Hom cochains are functorial in the coefficient representation. -/
def cochainsFunctor : Rep ℝ G ⥤ CochainComplex (ModuleCat ℝ) ℕ where
  obj := cochains G X
  map := cochainMap G X
  map_id := cochainMap_id G X
  map_comp := cochainMap_comp G X

/-- Coefficient postcomposition acts pointwise on equivariant singular simplex functions. -/
def functionMap {V W : Rep ℝ G} (φ : V ⟶ W) (n : ℕ) :
    equivariantFunctions G X V n →ₗ[ℝ] equivariantFunctions G X W n where
  toFun f := ⟨fun σ => φ.hom (f σ), fun g σ => by
    exact (congrArg (fun v => φ.hom v) (f.property g σ)).trans
      (congrArg (fun u => u (f σ)) (φ.hom.isIntertwining' g))⟩
  map_add' f h := by apply Subtype.ext; funext σ; exact map_add _ _ _
  map_smul' r f := by apply Subtype.ext; funext σ; exact map_smul _ _ _

/-- The literal cochain/function identification is natural in the coefficients. -/
theorem cochainFunctionEquiv_natural {V W : Rep ℝ G} (φ : V ⟶ W) (n : ℕ)
    (f : chainRep G X n ⟶ V) :
    cochainFunctionEquiv G X W n ((cochainMap G X φ).f n f)=
      functionMap G X φ n (cochainFunctionEquiv G X V n f) := rfl

/-- On actual singular generators, the Hom differential is the alternating face sum. -/
theorem evaluate_d (V : Rep ℝ G) (n : ℕ) (f : chainRep G X n ⟶ V)
    (σ : SingularSimplex X (n+1)) :
    cochainFunctionEquiv G X V (n+1) ((cochains G X V).d n (n+1) f) σ=
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        cochainFunctionEquiv G X V n f ((TopCat.toSSet.obj X).δ i σ) := by
  have h := congrArg (fun u => u.hom 1)
    ((TopCat.toSSet.obj X).ιChainComplex_d (R := ModuleCat.of ℝ ℝ) σ)
  simp only [ModuleCat.hom_sum,ModuleCat.hom_zsmul,
    LinearMap.sum_apply,LinearMap.smul_apply] at h
  let l : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℝ ℝ)).X n →ₗ[ℝ] V :=
    f.hom.toLinearMap
  have hf := congrArg (fun v => l v) h
  change f.hom ((equivariantD G X (n+1) n).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ) 1))=_
  simp only [map_sum, map_zsmul] at hf
  convert hf using 1 <;> rfl

end TernaryPoly.SmoothSingularGlobal
