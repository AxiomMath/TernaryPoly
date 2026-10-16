module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.CoveringNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Set SmoothCoveringDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The actual degree-two local comparison on an arithmetic quotient neighborhood, in the
coefficient frame of its specified covering chart. Global ordinary and compact-support descent
are separate obligations, not hypotheses discharged by this local isomorphism. -/
def degreeTwoQuotientLocalComparison (ρ : Representation ℝ DeckGroup F) (S : Space)
    {V : Set Coordinates} (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target)
    (hc : Convex ℝ V) (hne : V.Nonempty) :
    (coveringComplex ρ (chartOpen_isOpen S hV)).homology 2 ≅
      (realSingularCochains (TopCat.of (chartOpen S V)) (ModuleCat.of ℝ F)).homology 2 :=
  quotientLocalComparison ρ S hV hVt hc hne 2

end TernaryPoly.SmoothSingularComparison
