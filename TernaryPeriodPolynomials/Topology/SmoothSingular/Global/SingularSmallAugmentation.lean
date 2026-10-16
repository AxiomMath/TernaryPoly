module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.LocalSmallChains
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularFlagNaturality
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FlagZeroDifferential

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree Module
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

/-- Actual small-singular Hom cochains restrict to each actual Čech intersection by the genuine
local-to-small singular chain map. -/
def smallCechRestriction (k : ℕ) (t : Fin (k+1) → ι) :
    coveringSmallCochains ρ U hU Set.univ hcover ⟶ coveringCochains ρ (cechDomain U t) :=
  homPullback (localToSmallChains U hU hcover k t) (Rep.of ρ)

/-- The actual small-singular augmentation restricts to each actual cover component. -/
def smallCechAugmentationDegree (n : ℕ) :
    (coveringSmallCochains ρ U hU Set.univ hcover).X n →ₗ[ℝ] SingularCechTerms ρ U n 1 :=
  LinearMap.pi (fun t => ((smallCechRestriction ρ U hU hcover 0 t).f n).hom)

/-- The actual small-singular augmentation is a genuine morphism of singular cochain complexes. -/
def smallCechAugmentationChain : coveringSmallCochains ρ U hU Set.univ hcover ⟶
    (singularCechBicomplex ρ U).X 0 :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (smallCechAugmentationDegree ρ U hU hcover n)) (by
    intro n
    change ModuleCat.ofHom (smallCechAugmentationDegree ρ U hU hcover n) ≫
      (singularCechColumn ρ U 1).d n (n+1) = _
    simp only [singularCechColumn,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    funext t
    exact congrArg (fun f => f.hom w) ((smallCechRestriction ρ U hU hcover 0 t).comm n (n+1)))

/-- The actual small-singular restriction keeps literal generator evaluation. -/
theorem smallCechRestriction_evaluate (n k : ℕ) (t : Fin (k+1) → ι)
    (w : (coveringSmallCochains ρ U hU Set.univ hcover).X n)
    (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) :
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ) n
      ((smallCechRestriction ρ U hU hcover k t).f n w) σ =
        w.hom (coverSmallBasis U hU hcover n (localSimplexFlag U hU hcover n k t σ).point) := by
  exact congrArg (fun c => w.hom c)
    ((congrArg (localToSmallDegree U hU hcover k t n).hom
      (generatorBasis_apply (TopCat.of (CoverOpen (cechDomain U t))) n σ).symm).trans
        (localToSmallDegree_generator U hU hcover k t n σ))

/-- The genuine small-cochain augmentation is exactly the actual degree-zero flag differential
under the proved genuine generator identifications. -/
theorem smallCechAugmentation_toFlags (n : ℕ) (w : (coveringSmallCochains ρ U hU Set.univ hcover).X n) :
    singularCechToFlags ρ U hU hcover n 0 (smallCechAugmentationDegree ρ U hU hcover n w) =
      (smallSimplexIndexCover U hU hcover n).flagD ρ 0 (smallCochainToFlags ρ U hU hcover n w) := by
  apply Subtype.ext
  funext x
  have h := smallCechRestriction_evaluate ρ U hU hcover n 0 x.labels w (flagSimplex U hU hcover n 0 x)
  have hg := congrArg (fun y : SingularCoverFlag U hU hcover n 1 => w.hom (coverSmallBasis U hU hcover n y.point))
    (localSimplexFlag_flag U hU hcover n 0 x)
  have hf := (smallSimplexIndexCover U hU hcover n).flagD_zero_value ρ
    (smallCochainToFlags ρ U hU hcover n w) x
  exact (h.trans hg).trans hf.symm

/-- The actual small-singular augmentation is horizontally closed. -/
theorem smallCechAugmentation_horizontal : smallCechAugmentationChain ρ U hU hcover ≫
    (singularCechBicomplex ρ U).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  apply (singularCechFlagEquiv ρ U hU hcover n 1).injective
  change singularCechToFlags ρ U hU hcover n 1
    (horizontal (singularCechBicomplex ρ U) 0 n (smallCechAugmentationDegree ρ U hU hcover n w)) =
      singularCechToFlags ρ U hU hcover n 1 0
  rw [singularCechToFlags_d,smallCechAugmentation_toFlags,map_zero]
  exact (smallSimplexIndexCover U hU hcover n).flagD_one_zero ρ _

/-- The actual cover-small singular complex augments its genuine Čech–singular bicomplex. -/
def singularCechTotalAugmentation : TotalAugmentation
    (coveringSmallCochains ρ U hU Set.univ hcover) (singularCechBicomplex ρ U) where
  map := smallCechAugmentationChain ρ U hU hcover
  horizontal_zero := smallCechAugmentation_horizontal ρ U hU hcover

end TernaryPoly.SmoothSingularGlobal
