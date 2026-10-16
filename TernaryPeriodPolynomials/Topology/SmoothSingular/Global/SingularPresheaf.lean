module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Functoriality
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormPresheaf

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SymmetricSpaceCovering
variable {G : Type} [Group G] {X Y Z : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X]
  [MulAction G Y] [ContinuousConstSMul G Y]
  [MulAction G Z] [ContinuousConstSMul G Z]

/-- The actual equivariant singular chain map of the identity is the identity. -/
theorem equivariantChainMap_id :
    equivariantChainMap (𝟙 X) (fun _ _ => rfl) = 𝟙 (equivariantChains G X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (forget₂ (Rep ℝ G) (ModuleCat ℝ)).map_injective
  exact congrArg (fun k => k.f n)
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
      (ModuleCat.of ℝ ℝ)).map_id X)

/-- Genuine equivariant singular chain maps compose as the underlying continuous maps do. -/
theorem equivariantChainMap_comp (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (k : Y ⟶ Z) (hk : ∀ (g : G) (y : Y), k (g • y) = g • k y) :
    equivariantChainMap (f ≫ k) (fun g x => (congrArg k (hf g x)).trans (hk g (f x))) =
      equivariantChainMap f hf ≫ equivariantChainMap k hk := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (forget₂ (Rep ℝ G) (ModuleCat ℝ)).map_injective
  exact congrArg (fun a => a.f n)
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
      (ModuleCat.of ℝ ℝ)).map_comp f k)

/-- Pullback by the identity does not change the actual equivariant singular cochain. -/
theorem cochainPullback_id (V : Rep ℝ G) :
    cochainPullback (𝟙 X) (fun _ _ => rfl) V = 𝟙 (cochains G X V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (equivariantChains G X).X n ⟶ V at φ
  change (equivariantChainMap (𝟙 X) (fun _ _ => rfl)).f n ≫ φ = φ
  rw [equivariantChainMap_id]
  exact Category.id_comp φ

/-- Actual equivariant singular cochain pullbacks compose contravariantly. -/
theorem cochainPullback_comp (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (k : Y ⟶ Z) (hk : ∀ (g : G) (y : Y), k (g • y) = g • k y) (V : Rep ℝ G) :
    cochainPullback (f ≫ k) (fun g x => (congrArg k (hf g x)).trans (hk g (f x))) V =
      cochainPullback k hk V ≫ cochainPullback f hf V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (equivariantChains G Z).X n ⟶ V at φ
  change (equivariantChainMap (f ≫ k) _).f n ≫ φ =
    (equivariantChainMap f hf).f n ≫ ((equivariantChainMap k hk).f n ≫ φ)
  rw [equivariantChainMap_comp]
  exact Category.assoc _ _ _

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The real equivariant singular Hom complexes form an actual presheaf of complexes. -/
def singularComplexPresheaf :
    (Opens (TopCat.of OrbitSpace))ᵒᵖ ⥤ CochainComplex (ModuleCat ℝ) ℕ where
  obj U := coveringCochains ρ (U.unop : Set OrbitSpace)
  map f := coveringCochainRestriction ρ f.unop.le
  map_id U := cochainPullback_id (X := TopCat.of (CoverOpen (U.unop : Set OrbitSpace))) (Rep.of ρ)
  map_comp f g := (cochainPullback_comp (coverInclusion g.unop.le)
    (coverInclusion_equivariant g.unop.le) (coverInclusion f.unop.le)
    (coverInclusion_equivariant f.unop.le) (Rep.of ρ))

/-- Degree-n real equivariant singular cochains on actual quotient opens. -/
def singularPresheaf (n : ℕ) : TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace) :=
  singularComplexPresheaf ρ ⋙ HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.up ℕ) n

/-- The literal singular coboundary is a natural transformation of actual presheaves. -/
def singularPresheafDifferential (n : ℕ) : singularPresheaf ρ n ⟶ singularPresheaf ρ (n+1) where
  app U := (coveringCochains ρ (U.unop : Set OrbitSpace)).d n (n+1)
  naturality _ _ f := (coveringCochainRestriction ρ f.unop.le).comm n (n+1)

/-- The actual singular presheaf coboundary squares to zero. -/
theorem singularPresheafDifferential_squared (n : ℕ) :
    singularPresheafDifferential ρ n ≫ singularPresheafDifferential ρ (n+1) = 0 := by
  apply NatTrans.ext
  funext U
  exact (coveringCochains ρ (U.unop : Set OrbitSpace)).d_comp_d n (n+1) (n+1+1)

/-- The genuine real equivariant singular presheaf complex, before sheafification. -/
def singularPresheafComplex : CochainComplex (TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace)) ℕ :=
  CochainComplex.of (singularPresheaf ρ) (singularPresheafDifferential ρ)
    (singularPresheafDifferential_squared ρ)

end TernaryPoly.SmoothSingularGlobal
