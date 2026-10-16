module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionProjective

@[expose] public section


noncomputable section
open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial
namespace TernaryPoly.EquivariantSingularCohomology
open FreeActionLinearization EquivariantSingularResolution

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]
  (V : Rep ℚ G) (n : ℕ)

/-- Equivariant coefficient-valued functions on the actual Mathlib singular simplices. -/
abbrev equivariantFunctions : Submodule ℚ (SingularSimplex X n → V) where
  carrier := {f | ∀ (g : G) (σ : SingularSimplex X n), f (g • σ)=V.ρ g (f σ)}
  zero_mem' := by simp
  add_mem' := by intro f h hf hh g σ; simp only [Pi.add_apply,hf g σ,hh g σ,map_add]
  smul_mem' := by intro r f hf g σ; simp only [Pi.smul_apply,hf g σ,map_smul]

instance equivariantFunctions_coeFun :
    CoeFun (equivariantFunctions G X V n) (fun _ => SingularSimplex X n → V) := ⟨Subtype.val⟩

/-- Evaluate a representation morphism at the literal singular generator of coefficient one. -/
def evaluate : (chainRep G X n ⟶ V) →ₗ[ℚ] equivariantFunctions G X V n where
  toFun f := ⟨fun σ => f.hom (((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of ℚ ℚ) σ) 1),fun g σ => by
      have h := congrArg (fun u => u 1) (generator_smul G X n σ g)
      change f.hom (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) (g • σ)) 1)=_
      exact (congrArg (fun v => f.hom v) h).symm.trans (congrArg (fun u => u (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) σ) 1)) (f.hom.isIntertwining' g))⟩
  map_add' f h := by apply Subtype.ext; funext σ; rfl
  map_smul' r f := by apply Subtype.ext; funext σ; rfl

/-- The linear extension of a literal equivariant simplex function to actual singular chains. -/
def extendModule (f : equivariantFunctions G X V n) :
    (underlyingChains X).X n ⟶ ModuleCat.of ℚ V :=
  Sigma.desc (fun σ : SingularSimplex X n =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ V (f σ)))

@[simp] theorem generator_extendModule (f : equivariantFunctions G X V n)
    (σ : SingularSimplex X n) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ extendModule G X V n f=
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ V (f σ)) := Sigma.ι_comp_desc _ _

@[simp] theorem extendModule_generator (f : equivariantFunctions G X V n)
    (σ : SingularSimplex X n) (r : ℚ) :
    extendModule G X V n f (((TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℚ ℚ) σ) r)=r • f σ :=
  congrArg (fun u => u r) (generator_extendModule G X V n f σ)

/-- The linear extension is equivariant for the actual singular scalar action. -/
theorem extendModule_equivariant (f : equivariantFunctions G X V n) (g : G) :
    (scalarChainMap G X g).f n ≫ extendModule G X V n f=
      extendModule G X V n f ≫ ModuleCat.ofHom (V.ρ g) := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  have h := congrArg (fun u => u ≫ extendModule G X V n f) (generator_smul G X n σ g)
  have hh := congrArg (fun u => u ≫ ModuleCat.ofHom (V.ρ g))
    (generator_extendModule G X V n f σ)
  have hl : ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ V (f (g • σ)))=
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ V (f σ)) ≫ ModuleCat.ofHom (V.ρ g) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact (congrArg (fun v => r • v) (f.property g σ)).trans (map_smul _ _ _).symm
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((generator_extendModule G X V n f (g • σ)).trans
      (hl.trans ((Category.assoc _ _ _).symm.trans hh).symm)))

/-- The representation morphism associated to an equivariant simplex function. -/
def extend (f : equivariantFunctions G X V n) : chainRep G X n ⟶ V :=
  Rep.ofHom ⟨(extendModule G X V n f).hom, fun g =>
    congrArg ModuleCat.Hom.hom (extendModule_equivariant G X V n f g)⟩

@[simp] theorem evaluate_extend (f : equivariantFunctions G X V n) :
    evaluate G X V n (extend G X V n f)=f := by
  apply Subtype.ext
  funext σ
  change extendModule G X V n f (((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of ℚ ℚ) σ) 1)=f σ
  rw [extendModule_generator,one_smul]

/-- A linear map on the actual chain coproduct is determined by coefficient-one generators. -/
theorem evaluate_injective : Function.Injective (evaluate G X V n) := by
  intro f h heq
  apply (forget₂ (Rep ℚ G) (ModuleCat ℚ)).map_injective
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  ext
  exact congrArg (fun u : equivariantFunctions G X V n => u σ) heq

/-- Actual singular representation morphisms are precisely equivariant simplex functions. -/
def cochainFunctionEquiv : (chainRep G X n ⟶ V) ≃ₗ[ℚ] equivariantFunctions G X V n :=
  LinearEquiv.ofBijective (evaluate G X V n)
    ⟨evaluate_injective G X V n,fun f => ⟨extend G X V n f,evaluate_extend G X V n f⟩⟩

@[simp] theorem cochainFunctionEquiv_apply (f : chainRep G X n ⟶ V)
    (σ : SingularSimplex X n) :
    cochainFunctionEquiv G X V n f σ=
      f.hom (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ) 1) := rfl

end TernaryPoly.EquivariantSingularCohomology
