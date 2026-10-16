module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Representation
public import TernaryPeriodPolynomials.Analysis.Compact.FormFiniteCharts

@[expose] public section


/-! Finite chart decomposition for the actual polynomial coefficient representation. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold SmoothCoveringDeRham Set

theorem exists_finite_chart_decomposition (n k : ℕ)
    (w : CompactSupportForm (deckRepresentation n) univ k) :
    ∃ s : Finset Space, ∃ a : s → CompactSupportForm (deckRepresentation n) univ k,
      (∀ S, quotientSupport (a S).val ⊆ (quotientChart S.val).source) ∧ ∑ S, a S = w :=
  CompactFormFiniteCharts.exists_finite_chart_decomposition (deckRepresentation n) k w

end TernaryPoly.PolynomialFormCoordinates
