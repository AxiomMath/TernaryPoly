module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryProduct
public import TernaryPeriodPolynomials.Topology.Supported.InwardManifold

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientBoundary
open Topology SymmetricSpaceBordifiedPrincipalSix

/-- Every actual quotient point has an interior-preserving supported local deformation whose
endpoint is in the original arithmetic manifold. This uses the proved literal product charts. -/
theorem exists_local (q : BordifiedOrbit) :
    ∃ H : InwardHomotopy.LocalDeformation (Set.range arithmeticEmbedding),
      H.homotopy (1,q)∈Set.range arithmeticEmbedding := by
  let : T2Space BordifiedOrbit :=
    SymmetricSpaceCompactBordification.quotient_hausdorff IntegralGL3Congruence.principalSix
  obtain ⟨x,hx⟩ := productCharts_cover q
  exact SupportedInward.exists_localDeformation (Set.range arithmeticEmbedding)
    (productChart x) (fun y hy => productChart_interior x hy) q hx

end TernaryPoly.SymmetricSpaceQuotientBoundary
