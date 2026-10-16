module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryProduct
public import TernaryPeriodPolynomials.Topology.Supported.DownwardLocal

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryNeighborhood
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient
  IntegralGL3Congruence SymmetricSpaceQuotientBoundary
open scoped unitInterval

/-- Every actual arithmetic boundary point has a supported downward collapse preserving any
prescribed open neighborhood of the whole boundary and fixing that boundary pointwise. -/
theorem exists_local (W : Set BordifiedOrbit) (hW : IsOpen W)
    (hAW : boundary principalSix ⊆ W) (q : BordifiedOrbit) (hq : q ∈ boundary principalSix) :
    ∃ d : BoundaryNeighborhood.Deformation (boundary principalSix) W, ∃ V : Set BordifiedOrbit,
      IsOpen V ∧ q ∈ V ∧ ∀ y ∈ V, d.homotopy (1, y) ∈ boundary principalSix := by
  let : T2Space BordifiedOrbit := SymmetricSpaceCompactBordification.quotient_hausdorff principalSix
  obtain ⟨x, hx⟩ := productCharts_cover q
  exact SupportedDownward.exists_localDeformation (boundary principalSix) W hW hAW
    (productChart x) (fun y hy => productChart_boundary x hy) q hx hq

end TernaryPoly.SymmetricSpaceBoundaryNeighborhood
