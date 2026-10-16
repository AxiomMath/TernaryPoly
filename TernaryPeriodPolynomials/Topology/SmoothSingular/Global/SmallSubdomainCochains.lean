module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallSubdomainChains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  {V W : Set OrbitSpace} (hV : V ⊆ ⋃ i, U i) (hW : W ⊆ ⋃ i, U i) (hVW : V ⊆ W)

/-- Actual cover-small cochain restriction on genuine covering subdomains. -/
def smallSubdomainRestriction : coveringSmallCochains ρ U hU W hW ⟶
    coveringSmallCochains ρ U hU V hV :=
  homPullback (smallSubdomainChains U hU hV hW hVW) (Rep.of ρ)

/-- Restriction to an actual quotient subdomain commutes with literal small-chain restriction. -/
theorem smallSubdomainRestriction_square :
    coveringCochainRestriction ρ hVW ≫ coveringSmallRestriction ρ U hU V hV =
      coveringSmallRestriction ρ U hU W hW ≫ smallSubdomainRestriction ρ U hU hV hW hVW := by
  have h := congrArg (fun f => homPullback f (Rep.of ρ))
    (smallSubdomainChains_inclusion U hU hV hW hVW)
  rw [homPullback_comp,homPullback_comp] at h
  exact h.symm

end TernaryPoly.SmoothSingularGlobal
