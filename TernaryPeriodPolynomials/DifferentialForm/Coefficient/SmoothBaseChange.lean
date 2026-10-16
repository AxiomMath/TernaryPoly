module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Tensor
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.RealCoefficientNorm
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CoefficientExactness

@[expose] public section


/-! Literal smooth-form scalar extension for the rational polynomial deck coefficients. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open CategoryTheory SmoothSingularGlobal SmoothCoveringDeRham SymmetricSpaceCovering

abbrev rationalDeckCoefficientRep (n : ℕ) (e : ℤ) : Rep ℚ DeckGroup :=
  Rep.of (rationalDeckRepresentation n e)

instance rationalDeckCoefficientRep_finiteDimensional (n : ℕ) (e : ℤ) :
    FiniteDimensional ℚ (rationalDeckCoefficientRep n e) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℚ n)

instance extendedCoefficientFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (ExtendedCoefficients n) :=
  realRep_finiteDimensional (rationalDeckCoefficientRep n 0)

abbrev extendedCoefficientNorm (n : ℕ) : NormedAddCommGroup (ExtendedCoefficients n) :=
  realCoefficientNorm (rationalDeckCoefficientRep n 0)

abbrev extendedCoefficientNormedSpace (n : ℕ) :
    letI := extendedCoefficientNorm n; NormedSpace ℝ (ExtendedCoefficients n) :=
  realCoefficientNormedSpace (rationalDeckCoefficientRep n 0)

attribute [local instance] extendedCoefficientNorm extendedCoefficientNormedSpace

def coefficientScalarExtensionContinuous (n : ℕ) (e : ℤ) :
    realRep (rationalDeckCoefficientRep n e) ≃L[ℝ] Coefficients n :=
  (coefficientScalarExtension n : realRep (rationalDeckCoefficientRep n e) ≃ₗ[ℝ] Coefficients n).toContinuousLinearEquiv

theorem coefficientScalarExtensionContinuous_equivariant (n : ℕ) (e : ℤ)
    (g : DeckGroup) (z : realRep (rationalDeckCoefficientRep n e)) :
    coefficientScalarExtensionContinuous n e ((realRep (rationalDeckCoefficientRep n e)).ρ g z) =
      deckRepresentation n g (coefficientScalarExtensionContinuous n e z) :=
  coefficientScalarExtension_equivariant n e g z

theorem compactExact_realPolynomialCoefficients (n : ℕ) (e : ℤ)
    (h : CompactExactInDegree (deckRepresentation n) 1) :
    CompactExactInDegree (realRep (rationalDeckCoefficientRep n e)).ρ 1 :=
  compactExact_coefficient_transport (realRep (rationalDeckCoefficientRep n e)).ρ (deckRepresentation n)
    (coefficientScalarExtensionContinuous n e) (coefficientScalarExtensionContinuous_equivariant n e) 1 h

theorem rationalDeckCoefficientRep_eq_restriction (n : ℕ) (e : ℤ) :
    rationalDeckCoefficientRep n e =
      Rep.res deckPrincipal (SymmetricSpaceAllTopBoundary.polynomialCoefficients n e) := rfl

end TernaryPoly.PolynomialCoefficientMetric
