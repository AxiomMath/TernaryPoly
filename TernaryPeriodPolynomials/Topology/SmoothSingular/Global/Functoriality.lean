module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoverAction

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory FreeActionLinearization
variable {G : Type} [Group G] {X Y Z : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X]
  [MulAction G Y] [ContinuousConstSMul G Y]
  [MulAction G Z] [ContinuousConstSMul G Z]

/-- Actual equivariant continuous maps commute with the actual singular chain deck actions. -/
theorem singularMap_action (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (g : G) :
    scalarChainMap G X g ≫ SmoothSingularComparison.realSingularChainMap f =
      SmoothSingularComparison.realSingularChainMap f ≫ scalarChainMap G Y g := by
  have h : scalarMap G X g ≫ f = f ≫ scalarMap G Y g := by
    ext x
    exact hf g x
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg (fun k => ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
      (ModuleCat.of ℝ ℝ)).map k) h).trans (Functor.map_comp _ _ _))

/-- The actual real singular representation map induced by an equivariant continuous map. -/
def equivariantChainMap (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    equivariantChains G X ⟶ equivariantChains G Y where
  f n := Rep.ofHom ⟨((SmoothSingularComparison.realSingularChainMap f).f n).hom, fun g => by
    exact congrArg (fun k => (k.f n).hom) (singularMap_action f hf g)⟩
  comm' i j _ := by
    apply (forget₂ (Rep ℝ G) (ModuleCat ℝ)).map_injective
    exact (SmoothSingularComparison.realSingularChainMap f).comm i j

/-- Actual real equivariant Hom cochains pull back by precomposition with the genuine chain map. -/
def cochainPullback (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (V : Rep ℝ G) :
    cochains G Y V ⟶ cochains G X V where
  f n := ModuleCat.ofHom
    { toFun φ := (equivariantChainMap f hf).f n ≫ φ
      map_add' _ _ := by simp only [Preadditive.comp_add]
      map_smul' _ _ := by simp only [Linear.comp_smul, RingHom.id_apply] }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (equivariantChains G Y).X i ⟶ V at φ
    change (equivariantChains G X).d j i ≫ ((equivariantChainMap f hf).f i ≫ φ) =
      (equivariantChainMap f hf).f j ≫ ((equivariantChains G Y).d j i ≫ φ)
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k ≫ φ) ((equivariantChainMap f hf).comm j i).symm

/-- Actual pullback and coefficient postcomposition commute before passing to cohomology. -/
theorem cochainPullback_coefficient (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    {V W : Rep ℝ G} (u : V ⟶ W) :
    cochainPullback f hf V ≫ cochainMap G X u =
      cochainMap G Y u ≫ cochainPullback f hf W := by
  ext n φ
  rfl

/-- The actual restriction map of real equivariant singular cochains over quotient opens. -/
def coveringCochainRestriction {F : Type} [AddCommGroup F] [Module ℝ F]
    (ρ : Representation ℝ SymmetricSpaceCovering.DeckGroup F)
    {U V : Set SymmetricSpaceCovering.OrbitSpace} (hVU : V ⊆ U) :
    coveringCochains ρ U ⟶ coveringCochains ρ V :=
  cochainPullback (coverInclusion hVU) (coverInclusion_equivariant hVU) (Rep.of ρ)

end TernaryPoly.SmoothSingularGlobal
