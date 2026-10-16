module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Presentation
public import TernaryPeriodPolynomials.Building.BoundaryApartments.BridgeAssembly
public import TernaryPeriodPolynomials.Building.BoundaryApartments.CuspReflectionPrimitive
public import TernaryPeriodPolynomials.Building.BoundaryApartments.IncidentGoodBoundary
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.PathDefects
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Surjectivity
public import TernaryPeriodPolynomials.Building.BoundaryApartments.PolynomialFunctionalConstruction

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge

theorem polynomial_boundary_bridge (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) : PolynomialBoundaryBridge f := by
  exact Helpers.polynomialBoundaryBridge_of_functional hn hf
    (Helpers.polynomialEdgeFunctional hf) (Helpers.polynomialEdgeFunctional_property hf)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge
