module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.EvenCase
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.OddCase
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.InnerPlaneEdgeParabolicProof
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.CuspidalSupply
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlaneSupply

@[expose] public section


/-! Targets: the spanning statements of Lemma C.3 (`ar:lem:seed`) — Eichler–Shimura at each cusp
type, in the project's adelic boundary model. Together with the existing bad-line span
(`TernaryPeriodPolynomials.Automorphic.DirectFinal.inner_bad_line_n_plus_three_final`) they say that the
mixed cuspidal face classes are spanned by the classes of cuspidal data. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.CuspidalSpan

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Bad-plane span.** A mixed cuspidal plane class that vanishes at every good plane lies in the
span of the plane summands of cuspidal data (the bad-plane Levi is `GL₂(ℤ)`; level-one
Eichler–Shimura).

For even `n` the whole bad-plane local cohomology vanishes
(`TernaryPeriodPolynomials.Argument.CuspidalSpan.EvenCase.bad_plane_cuspidal_span_even`). For odd `n`,
`TernaryPeriodPolynomials.Argument.CuspidalSpan.OddCase.bad_plane_cuspidal_span_odd` uses two inputs: an inner class has a
parabolic bad-plane edge (`InnerPlaneEdgeParabolicProof.innerPlaneEdgeParabolic_proof`), and every
parabolic class is the edge of an element of the span vanishing at the good plane
(`BadPlaneSupply.cuspFormRealized`: the seeds of the plane sources of Eichler inputs, cut off to the
bad plane, realize the period class of every level-one cusp form). -/
theorem bad_plane_cuspidal_span (n : ℕ) (hn : 0 < n) (ξ : StratumH2 n trivialCharacter .plane)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hinner : InnerBoundary n trivialCharacter .plane ξ) :
    ξ ∈ automorphicPlaneSpan n := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact bad_plane_cuspidal_span_even n hn heven ξ hgood
  · exact bad_plane_cuspidal_span_odd n hn hodd
      (innerPlaneEdgeParabolic_proof hn hodd)
      (parabolicPeriodRealized_of_cuspFormRealized n hn hodd (cuspFormRealized n hn hodd))
      ξ hgood hinner

end TernaryPeriodPolynomials
