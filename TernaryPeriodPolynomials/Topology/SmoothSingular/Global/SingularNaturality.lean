module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SymmetricSpaceCovering FreeActionLinearization
open scoped Simplicial
variable {G : Type} [Group G] {X Y : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X] [MulAction G Y] [ContinuousConstSMul G Y]

/-- An actual real singular generator maps to its postcomposition with the given continuous map. -/
theorem singularGenerator_map (f : X ⟶ Y) (n : ℕ) (σ : SingularSimplex X n) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (SmoothSingularComparison.realSingularChainMap f).f n =
      (TopCat.toSSet.obj Y).ιChainComplex ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ) :=
  SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map f) (ModuleCat.of ℝ ℝ) σ

/-- Pullback of genuine equivariant singular Hom cochains is actual simplex postcomposition. -/
theorem cochainPullback_evaluate (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (V : Rep ℝ G) (n : ℕ) (c : chainRep G Y n ⟶ V) (σ : SingularSimplex X n) :
    cochainFunctionEquiv G X V n ((cochainPullback f hf V).f n c) σ =
      cochainFunctionEquiv G Y V n c ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ) := by
  exact congrArg (fun m => c.hom (m.hom 1)) (singularGenerator_map f n σ)

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The actual coefficient-to-singular map commutes with genuine open restriction. -/
theorem coefficientSingularMap_restrict {U V : Set OrbitSpace} (hVU : V ⊆ U)
    (f : coefficientSections ρ U) :
    (coveringCochainRestriction ρ hVU).f 0 (coefficientSingularMap ρ U f) =
      coefficientSingularMap ρ V (coefficientRestriction ρ hVU f) := by
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen V)) (Rep.of ρ) 0).injective
  apply Subtype.ext
  funext σ
  erw [cochainPullback_evaluate]
  rw [coefficientSingularMap_eval, coefficientSingularMap_eval]
  rfl

/-- The genuine natural coefficient-to-singular augmentation on quotient opens. -/
def coefficientToSingular : coefficientPresheaf ρ ⟶ singularPresheaf ρ 0 where
  app U := ModuleCat.ofHom (coefficientSingularMap ρ (U.unop : Set OrbitSpace))
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (coefficientSingularMap_restrict ρ f.unop.le s).symm

/-- The actual singular presheaf augmentation is closed as a natural transformation. -/
theorem coefficientToSingular_closed :
    coefficientToSingular ρ ≫ singularPresheafDifferential ρ 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact coefficientSingularMap_closed ρ (U.unop : Set OrbitSpace) f

end TernaryPoly.SmoothSingularGlobal
