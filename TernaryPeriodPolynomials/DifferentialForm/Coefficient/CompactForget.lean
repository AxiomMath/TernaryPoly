module

public import TernaryPeriodPolynomials.DifferentialForm.Coefficient.SmoothBaseChange
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactExactVanishing
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactSheets
public import TernaryPeriodPolynomials.DifferentialForm.Principal.CompactForget

@[expose] public section


/-! Literal scalar extension and cover reindexing carry smooth exactness to the rational gate. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open CategoryTheory SmoothSingularGlobal SmoothCoveringDeRham SymmetricSpaceCovering
open CompactInteriorRelativeBoundary SymmetricSpaceAllTopBoundary

local instance polynomialOriginalCoverFact :
    Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

attribute [local instance] extendedCoefficientNorm extendedCoefficientNormedSpace

theorem rationalDeck_compactForget_zero_of_smooth_exact (n : ℕ) (e : ℤ)
    (h : CompactExactInDegree (deckRepresentation n) 1) :
    compactForget singularCoveringProjection (rationalDeckCoefficientRep n e) 2 = 0 :=
  originalCompactForget_eq_zero_of_smooth_exact (rationalDeckCoefficientRep n e) compactConvexCover
    (compactExact_realPolynomialCoefficients n e h)

theorem principalPolynomial_compactForget_zero_of_smooth_exact (n : ℕ) (e : ℤ)
    (h : CompactExactInDegree (deckRepresentation n) 1) :
    compactForget SymmetricSpaceBordifiedCohomology.interiorCover (polynomialCoefficients n e) 2 = 0 :=
  PolynomialFormPrincipalCover.principal_compactForget_zero (polynomialCoefficients n e)
    (rationalDeck_compactForget_zero_of_smooth_exact n e h)

theorem positivePolynomialInnerVanishing_of_smooth_exact
    (h : ∀ n : ℕ, 0 < n → CompactExactInDegree (deckRepresentation n) 1) :
    PositivePolynomialInnerVanishing := by
  intro n hn e
  exact principalPolynomial_compactForget_zero_of_smooth_exact n e (h n hn)

end TernaryPoly.PolynomialCoefficientMetric
