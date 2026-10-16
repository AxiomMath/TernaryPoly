module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.PlaneSupply

@[expose] public section


/-! Target: the good-plane spanning statement of Lemma C.3 (`ar:lem:seed`). -/

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Good-plane span.** The good-plane coordinate of every mixed cuspidal plane class is that of
an element of the span of the plane summands of cuspidal data (the good-plane Levi has level
three; Eichler–Shimura at level three). -/
theorem good_plane_cuspidal_span (n : ℕ) (hn : 0 < n) (ξ : StratumH2 n trivialCharacter .plane)
    (hinner : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ ξ' ∈ automorphicPlaneSpan n, VanishesOnGood n trivialCharacter .plane (ξ - ξ') :=
  TernaryPeriodPolynomials.Argument.GoodPlaneSpan.good_plane_cuspidal_span_of_inputs n hn
    (TernaryPeriodPolynomials.Argument.GoodPlaneSpan.goodPlaneEdgeParabolic n hn)
    (TernaryPeriodPolynomials.Argument.GoodPlaneSpan.goodPlanePeriodsRealized n hn) ξ hinner

end TernaryPeriodPolynomials
