module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeGoodCusps.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps

theorem away_three_hecke_good_cusps : ∀ n : ℕ, 0 < n → ∀ D : InducingData n,
    ∀ hecke : BoundaryHecke n D.chi, ActualBoundaryHecke n D.chi hecke →
    ∀ t : HeckeCorrespondence, AwayThree t → ∀ b : BoundaryCoordinates n D.chi,
    GoodBoundaryVanishing n D.chi b → GoodBoundaryVanishing n D.chi (pairHecke D hecke t b) := by
  intro degree _ inducing hecke hhecke correspondence haway coordinates hgood
  exact ⟨Helpers.hecke_vanishes_on_good degree inducing.chi hecke hhecke correspondence
    haway .plane coordinates.1 hgood.1,
    Helpers.hecke_vanishes_on_good degree inducing.chi hecke hhecke correspondence
      haway .line coordinates.2 hgood.2⟩

end TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps
