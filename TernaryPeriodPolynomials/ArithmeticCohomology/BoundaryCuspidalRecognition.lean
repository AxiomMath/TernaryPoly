module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryHeckeDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.CuspidalSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalAssociateProjector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralRecovery

@[expose] public section


/-! The parent recognition statement, composed from the proved Hecke descent and
the three recognition children. -/

open GeneralEisenstein

namespace TernaryPeriodPolynomials

theorem boundary_cuspidal_recognition (n : ℕ) (hn : 0 < n)
    (b : BoundaryCoordinates n trivialCharacter)
    (hgood : GoodBoundaryVanishing n trivialCharacter b)
    (hinner : InnerBoundary n trivialCharacter .line b.2) :
    CuspidalRecognition n b := by
  exact boundary_cuspidal_recognition_of_pieces
    { hecke := TernaryPeriodPolynomials.BoundaryHeckeDescent.boundary_hecke_descent
      span := inner_bad_line_cuspidal_span
      projectors := cuspidal_associate_projector
      recovery := cuspidal_finite_spectral_recovery }
    n hn b hgood hinner

end TernaryPeriodPolynomials
