module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallRelativeSupport
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarCompact

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory Limits HomologicalComplex TopologicalSpace
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))

/-- Literal ordinary-to-small restriction is an epimorphism of cochain complexes. -/
instance coveringSmallRestriction_epi (V : Set OrbitSpace) (hV : V ⊆ ⋃ i, U i) :
    Epi (coveringSmallRestriction ρ U hU V hV) :=
  epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr
    (coveringSmallRestriction_surjective ρ U hU hV n))

/-- Actual small cochain restriction composes on genuine nested quotient subdomains. -/
theorem smallSubdomainRestriction_comp {V W Z : Set OrbitSpace}
    (hV : V ⊆ ⋃ i, U i) (hW : W ⊆ ⋃ i, U i) (hZ : Z ⊆ ⋃ i, U i)
    (hVW : V ⊆ W) (hWZ : W ⊆ Z) :
    smallSubdomainRestriction ρ U hU hW hZ hWZ ≫ smallSubdomainRestriction ρ U hU hV hW hVW =
      smallSubdomainRestriction ρ U hU hV hZ (hVW.trans hWZ) := by
  apply (cancel_epi (coveringSmallRestriction ρ U hU Z hZ)).mp
  rw [←Category.assoc,←smallSubdomainRestriction_square,Category.assoc,
    ←smallSubdomainRestriction_square,←Category.assoc,realCoverRestriction_comp (Rep.of ρ),
    smallSubdomainRestriction_square]

variable (hcover : Set.univ ⊆ ⋃ i, U i)

/-- The actual small-cochain restriction to the complement of a quotient support. -/
abbrev smallSupportRestriction (K : Set OrbitSpace) :=
  smallSubdomainRestriction ρ U hU ((subset_univ Kᶜ).trans hcover) hcover (subset_univ Kᶜ)

/-- Actual complement-relative small singular cochains. -/
abbrev smallSupport (K : Set OrbitSpace) := kernel (smallSupportRestriction ρ U hU hcover K)

/-- Actual small support enlargement retains the same ambient small cochain. -/
def smallSupportMap (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    smallSupport ρ U hU hcover K ⟶ smallSupport ρ U hU hcover L :=
  kernel.lift _ (kernel.ι _) (by
    dsimp only [smallSupportRestriction]
    rw [←smallSubdomainRestriction_comp ρ U hU ((subset_univ Lᶜ).trans hcover)
      ((subset_univ Kᶜ).trans hcover) hcover (compl_subset_compl.mpr hKL) (subset_univ Kᶜ),
      ←Category.assoc,kernel.condition,zero_comp])

/-- Genuine support enlargement preserves the literal map to absolute small cochains. -/
theorem smallSupportMap_forget (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    smallSupportMap ρ U hU hcover K L hKL ≫ kernel.ι (smallSupportRestriction ρ U hU hcover L) =
      kernel.ι (smallSupportRestriction ρ U hU hcover K) := kernel.lift_ι _ _ _

/-- Actual small support enlargement is the identity at equal supports. -/
theorem smallSupportMap_id (K : Set OrbitSpace) :
    smallSupportMap ρ U hU hcover K K (Subset.refl K) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (smallSupportRestriction ρ U hU hcover K))).mp
  rw [smallSupportMap_forget,Category.id_comp]

/-- Genuine small support enlargement composes. -/
theorem smallSupportMap_comp (K L M : Set OrbitSpace) (hKL : K ⊆ L) (hLM : L ⊆ M) :
    smallSupportMap ρ U hU hcover K L hKL ≫ smallSupportMap ρ U hU hcover L M hLM =
      smallSupportMap ρ U hU hcover K M (hKL.trans hLM) := by
  apply (cancel_mono (kernel.ι (smallSupportRestriction ρ U hU hcover M))).mp
  rw [Category.assoc,smallSupportMap_forget,smallSupportMap_forget,smallSupportMap_forget]

/-- The actual diagram of complement-relative small complexes over all genuine compact supports. -/
def smallSupportDiagram : Compacts OrbitSpace ⥤ CochainComplex (ModuleCat.{0} ℝ) ℕ where
  obj K := smallSupport ρ U hU hcover K
  map f := smallSupportMap ρ U hU hcover _ _ (leOfHom f)
  map_id K := smallSupportMap_id ρ U hU hcover K
  map_comp f g := (smallSupportMap_comp ρ U hU hcover _ _ _ (leOfHom f) (leOfHom g)).symm

/-- The genuine compact small-relative cohomology diagram. -/
def smallCompactDiagram (n : ℕ) : Compacts OrbitSpace ⥤ ModuleCat.{0} ℝ :=
  smallSupportDiagram ρ U hU hcover ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n

/-- The actual support-forgetting cocone on compact small-relative cohomology. -/
def smallCompactForgetCocone (n : ℕ) : Cocone (smallCompactDiagram ρ U hU hcover n) where
  pt := (coveringSmallCochains ρ U hU univ hcover).homology n
  ι := {
    app K := homologyMap (kernel.ι (smallSupportRestriction ρ U hU hcover K)) n
    naturality K L f := by
      change homologyMap (smallSupportMap ρ U hU hcover K L (leOfHom f)) n ≫ _ = _ ≫ 𝟙 _
      rw [Category.comp_id,←homologyMap_comp,smallSupportMap_forget] }

end TernaryPoly.SmoothSingularGlobal
