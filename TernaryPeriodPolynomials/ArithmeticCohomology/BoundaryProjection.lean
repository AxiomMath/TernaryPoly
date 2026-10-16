module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeGoodCusps
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.AssociateProjector

@[expose] public section


/-! The parent projection statement, composed from the proved away-three Hecke
stability and the away-three algebra child. -/

open GeneralEisenstein

namespace TernaryPeriodPolynomials

theorem boundary_projection_good_cusps (n : ℕ) (hn : 0 < n) (D : InducingData n)
    (hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (hhecke : ∀ side, RealizesHecke
      (flagRepresentation (rationalCoefficientComponent n D.chi) side) (hecke side))
    (p : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hp : IsIsotypicalProjection D hecke p)
    (b : BoundaryCoordinates n D.chi) (hb : GoodBoundaryVanishing n D.chi b) :
    GoodBoundaryVanishing n D.chi (p b) := by
  exact boundary_projection_good_cusps_of_pieces
    { stability := TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.away_three_hecke_good_cusps
      algebra := associate_projector_away_three_algebra }
    n hn D hecke hhecke p hp b hb

end TernaryPeriodPolynomials
