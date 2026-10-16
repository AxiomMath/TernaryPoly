module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallFlagCoefficients
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularCechFlags

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree Module
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

/-- The literal inclusion from the actual small-chain complex into actual global chains. -/
abbrev coverSmallInclusion : coveringSmallChains U hU Set.univ hcover ⟶
    equivariantChains DeckGroup (TopCat.of (CoverOpen Set.univ)) :=
  smallInclusion DeckGroup (TopCat.of (CoverOpen Set.univ)) (liftedOpenCover U hU Set.univ hcover)
    (liftedOpenCover_invariant U hU Set.univ hcover)

/-- Literal small-chain inclusion is injective degreewise. -/
instance coverSmallInclusion_mono (n : ℕ) : Mono ((coverSmallInclusion U hU hcover).f n) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- The actual singular generator basis intertwines the actual scalar action. -/
theorem generatorBasis_smul {G : Type} [Group G] (X : TopCat.{0}) [MulAction G X]
    [ContinuousConstSMul G X] (n : ℕ) (g : G) (σ : SingularSimplex X n) :
    chainAction G X n g (generatorBasis X n σ) = generatorBasis X n (g • σ) :=
  (congrArg (chainAction G X n g) (generatorBasis_apply X n σ)).trans
    ((chainAction_generator G X n g σ).trans (generatorBasis_apply X n (g • σ)).symm)

/-- Linear extension on the actual local singular basis into the actual small-chain module. -/
def localToSmallLinear (k : ℕ) (t : Fin (k+1) → ι) (n : ℕ) :
    (underlyingChains (TopCat.of (CoverOpen (cechDomain U t)))).X n →ₗ[ℝ]
      ((coveringSmallChains U hU Set.univ hcover).X n) :=
  (generatorBasis (TopCat.of (CoverOpen (cechDomain U t))) n).constr ℝ
    (fun σ => coverSmallBasis U hU hcover n (localSimplexFlag U hU hcover n k t σ).point)

/-- The actual local-to-small linear extension preserves literal basis generators. -/
theorem localToSmallLinear_generator (k : ℕ) (t : Fin (k+1) → ι) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) :
    localToSmallLinear U hU hcover k t n (generatorBasis (TopCat.of (CoverOpen (cechDomain U t))) n σ) =
      coverSmallBasis U hU hcover n (localSimplexFlag U hU hcover n k t σ).point :=
  Basis.constr_basis _ ℝ _ σ

/-- Equivariance of the actual linear extension, checked on one literal generator. -/
theorem localToSmallLinear_generator_equivariant (k : ℕ) (t : Fin (k+1) → ι) (n : ℕ)
    (g : DeckGroup) (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) :
    localToSmallLinear U hU hcover k t n
      (chainAction DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) n g
        (generatorBasis (TopCat.of (CoverOpen (cechDomain U t))) n σ)) =
      ((coveringSmallChains U hU Set.univ hcover).X n).ρ g
        (localToSmallLinear U hU hcover k t n (generatorBasis (TopCat.of (CoverOpen (cechDomain U t))) n σ)) := by
  have h₁ := congrArg (localToSmallLinear U hU hcover k t n)
    (generatorBasis_smul (TopCat.of (CoverOpen (cechDomain U t))) n g σ)
  have h₂ := localToSmallLinear_generator U hU hcover k t n (g • σ)
  have h₃ := congrArg (fun x : SingularCoverFlag U hU hcover n (k+1) => coverSmallBasis U hU hcover n x.point)
    (localSimplexFlag_smul U hU hcover n k t g σ)
  have h₄ := (coverSmallBasis_smul U hU hcover n g (localSimplexFlag U hU hcover n k t σ).point).symm
  have h₅ := congrArg (((coveringSmallChains U hU Set.univ hcover).X n).ρ g)
    (localToSmallLinear_generator U hU hcover k t n σ).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- The actual local-to-small linear extension intertwines the genuine deck actions. -/
theorem localToSmallLinear_equivariant (k : ℕ) (t : Fin (k+1) → ι) (n : ℕ) (g : DeckGroup) :
    (localToSmallLinear U hU hcover k t n).comp
      (chainAction DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) n g) =
    (((coveringSmallChains U hU Set.univ hcover).X n).ρ g).comp (localToSmallLinear U hU hcover k t n) :=
  (generatorBasis (TopCat.of (CoverOpen (cechDomain U t))) n).ext
    (localToSmallLinear_generator_equivariant U hU hcover k t n g)

/-- Actual local singular chains on an intersection include into actual cover-small global chains. -/
def localToSmallDegree (k : ℕ) (t : Fin (k+1) → ι) (n : ℕ) :
    chainRep DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) n ⟶
      (coveringSmallChains U hU Set.univ hcover).X n :=
  Rep.ofHom ⟨localToSmallLinear U hU hcover k t n,localToSmallLinear_equivariant U hU hcover k t n⟩

/-- The genuine local-to-small map preserves the literal simplex generator. -/
theorem localToSmallDegree_generator (k : ℕ) (t : Fin (k+1) → ι) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) :
    (localToSmallDegree U hU hcover k t n).hom (generatorBasis (TopCat.of (CoverOpen (cechDomain U t))) n σ) =
      coverSmallBasis U hU hcover n (localSimplexFlag U hU hcover n k t σ).point :=
  localToSmallLinear_generator U hU hcover k t n σ

/-- Composing the genuine local-to-small map with literal small inclusion is the actual
singular chain map of the genuine covering-subdomain inclusion. -/
theorem localToSmallDegree_inclusion (k : ℕ) (t : Fin (k+1) → ι) (n : ℕ) :
    localToSmallDegree U hU hcover k t n ≫ (coverSmallInclusion U hU hcover).f n =
      (equivariantChainMap (coverInclusion (Set.subset_univ (cechDomain U t)))
        (coverInclusion_equivariant (Set.subset_univ (cechDomain U t)))).f n := by
  apply (forget₂ (Rep ℝ DeckGroup) (ModuleCat ℝ)).map_injective
  apply ModuleCat.hom_ext
  apply (generatorBasis (TopCat.of (CoverOpen (cechDomain U t))) n).ext
  intro σ
  have h₁ := congrArg Subtype.val (localToSmallDegree_generator U hU hcover k t n σ)
  have h₂ := predicateBasis_apply (TopCat.of (CoverOpen Set.univ)) n
    (IsSmallSimplex (liftedOpenCover U hU Set.univ hcover)) (localSimplexFlag U hU hcover n k t σ).point
  have h₃ := congrArg (fun f => f.hom 1)
    (singularGenerator_map (coverInclusion (Set.subset_univ (cechDomain U t))) n σ)
  exact h₁.trans (h₂.trans ((congrArg
    (((SmoothSingularComparison.realSingularChainMap (coverInclusion (Set.subset_univ (cechDomain U t)))).f n).hom)
      (generatorBasis_apply (TopCat.of (CoverOpen (cechDomain U t))) n σ)).trans h₃).symm)

/-- A degreewise factorization through an actual monomorphic chain map is a genuine chain map. -/
def complexLiftThroughMono {C D E : ChainComplex (Rep.{0} ℝ DeckGroup) ℕ}
    (i : D ⟶ E) [∀ n, Mono (i.f n)] (f : C ⟶ E) (g : ∀ n, C.X n ⟶ D.X n)
    (hg : ∀ n, g n ≫ i.f n = f.f n) : C ⟶ D where
  f := g
  comm' a b _ := by
    apply (cancel_mono (i.f b)).mp
    rw [Category.assoc,← i.comm a b,← Category.assoc,hg,Category.assoc,hg]
    exact f.comm a b

/-- The actual local-to-small chain map, with commutation proved through the injective actual
small-chain inclusion and genuine singular functoriality. -/
def localToSmallChains (k : ℕ) (t : Fin (k+1) → ι) :
    equivariantChains DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) ⟶
      coveringSmallChains U hU Set.univ hcover :=
  complexLiftThroughMono (coverSmallInclusion U hU hcover)
    (equivariantChainMap (coverInclusion (Set.subset_univ (cechDomain U t)))
      (coverInclusion_equivariant (Set.subset_univ (cechDomain U t))))
    (localToSmallDegree U hU hcover k t) (localToSmallDegree_inclusion U hU hcover k t)

end TernaryPoly.SmoothSingularGlobal
