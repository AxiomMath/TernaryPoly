module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.KernelComparison
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallRestrictionSurjective

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory Limits HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  {V W : Set OrbitSpace} (hV : V ⊆ ⋃ i, U i) (hW : W ⊆ ⋃ i, U i) (hVW : V ⊆ W)

/-- Ordinary restriction on genuine covering subdomains is an epimorphism of complexes. -/
instance coveringCochainRestriction_epi : Epi (coveringCochainRestriction ρ hVW) :=
  epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr
    (coveringCochainRestriction_surjective ρ hVW n))

/-- Small-cochain restriction on genuine covering subdomains is an epimorphism of complexes. -/
instance smallSubdomainRestriction_epi : Epi (smallSubdomainRestriction ρ U hU hV hW hVW) :=
  epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr
    (smallSubdomainRestriction_surjective ρ U hU hV hW hVW n))

/-- Literal small-simplex restriction between the actual relative kernels of genuine subdomains. -/
def smallRelativeRestriction : kernel (coveringCochainRestriction ρ hVW) ⟶
    kernel (smallSubdomainRestriction ρ U hU hV hW hVW) :=
  kernel.map _ _ (coveringSmallRestriction ρ U hU W hW) (coveringSmallRestriction ρ U hU V hV)
    (smallSubdomainRestriction_square ρ U hU hV hW hVW)

/-- The genuine relative small-simplex restriction preserves the literal absolute cochain. -/
theorem smallRelativeRestriction_forget : smallRelativeRestriction ρ U hU hV hW hVW ≫
    kernel.ι (smallSubdomainRestriction ρ U hU hV hW hVW) =
      kernel.ι (coveringCochainRestriction ρ hVW) ≫ coveringSmallRestriction ρ U hU W hW := by
  simp [smallRelativeRestriction,kernel.map]

/-- Actual small-simplex restriction is a quasi-isomorphism of genuine relative kernels in all degrees. -/
instance smallRelativeRestriction_quasiIso : QuasiIso (smallRelativeRestriction ρ U hU hV hW hVW) := by
  let := coveringSmallRestriction_quasiIso ρ U hU V hV
  let := coveringSmallRestriction_quasiIso ρ U hU W hW
  exact RealCochainExcision.kernel_map_quasiIso _ _ _ _
    (smallSubdomainRestriction_square ρ U hU hV hW hVW)

/-- Genuine relative singular and relative small-singular cohomology are canonically isomorphic. -/
def smallRelativeCohomologyIso (n : ℕ) : (kernel (coveringCochainRestriction ρ hVW)).homology n ≅
    (kernel (smallSubdomainRestriction ρ U hU hV hW hVW)).homology n :=
  isoOfQuasiIsoAt (smallRelativeRestriction ρ U hU hV hW hVW) n

/-- The genuine relative cohomology comparison commutes with the actual forget-relative map. -/
theorem smallRelativeCohomologyIso_forget (n : ℕ) :
    (smallRelativeCohomologyIso ρ U hU hV hW hVW n).hom ≫
      homologyMap (kernel.ι (smallSubdomainRestriction ρ U hU hV hW hVW)) n =
        homologyMap (kernel.ι (coveringCochainRestriction ρ hVW)) n ≫
          homologyMap (coveringSmallRestriction ρ U hU W hW) n := by
  change homologyMap (smallRelativeRestriction ρ U hU hV hW hVW) n ≫ _ = _
  rw [←homologyMap_comp,smallRelativeRestriction_forget,homologyMap_comp]

end TernaryPoly.SmoothSingularGlobal
