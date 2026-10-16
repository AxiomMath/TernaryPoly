module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.Assembly
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicUpperLegZero
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicLowerLegZero
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicSigmaPrimitive
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicSigmaPrimitiveOpp
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Functional

@[expose] public section


/-!
# Assembly: `GoodPlaneEdgeParabolic`, both legs combined

Combines the two legs proved separately — `EdgeParabolicUpperLegZero.lean`
(`edgeParabolic_goodPlaneEdgeCocycle_upper_eq_zero`, via the base edge `mk gF` and
`EdgeParabolicSigmaPrimitive.lean`'s `edgeParabolic_sigmaPrimitive_of_innerBoundary`) and
`EdgeParabolicLowerLegZero.lean` (`edgeParabolic_goodPlaneEdgeCocycle_lower_eq_zero`, via the
opposite edge `mk (gF * τ)` and `EdgeParabolicSigmaPrimitiveOpp.lean`'s
`edgeParabolic_sigmaPrimitive_of_innerBoundaryOpp`) — with the Hecke-free membership criterion
`LevelThreeBoundaryFunctional.mem_parabolicH1_iff` (`betaInf = 0 ∧ betaZero = 0`), to prove
`GoodPlaneEdgeParabolic n hn`: the input left by `Assembly.lean`'s
`good_plane_cuspidal_span_of_inputs`.

For a given `ξ`/`inner`, the two legs produce cocycles `C`/`C'` representing the *same* class
`cuspRes n trivialCharacter .plane true ξ` (via each leg's own `hx`, oriented
`classOf ... = cuspRes ...`), but need not be literally equal; each leg only needs to control its
own cusp value, so no comparison between the two cocycles is required.
-/

noncomputable section

open TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryFunctional
  (betaInf_mk betaZero_mk mem_parabolicH1_iff)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (goodPlaneEdgeCocycle)

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-- **Input 1, discharged**: the good-plane edge of the good Shapiro coordinate of an
`InnerBoundary` class is parabolic — `betaInf = 0` via the base edge's upper leg,
`betaZero = 0` via the opposite edge's lower leg. -/
theorem goodPlaneEdgeParabolic (n : ℕ) (hn : 0 < n) : GoodPlaneEdgeParabolic n hn := by
  intro ξ inner
  rw [mem_parabolicH1_iff]
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hx, primitive, hprimitive⟩ := edgeParabolic_sigmaPrimitive_of_innerBoundary inner
    rw [← hx, edgeParabolic_goodPlaneEdge_eq hn C primitive hprimitive]
    have hbridge : qcls (levelRep (n + 1) (-1))
        (goodPlaneEdgeCocycle (edgeParabolic_cycle C primitive hprimitive)) =
        Submodule.Quotient.mk (goodPlaneEdgeCocycle (edgeParabolic_cycle C primitive hprimitive)) :=
      rfl
    rw [hbridge, betaInf_mk, edgeParabolic_goodPlaneEdgeCocycle_upper_eq_zero C primitive hprimitive]
    simp
  · obtain ⟨C, hx, primitive, hprimitive⟩ :=
      edgeParabolic_sigmaPrimitive_of_innerBoundaryOpp inner
    rw [← hx, edgeParabolic_goodPlaneEdge_eqOpp hn C primitive hprimitive]
    have hbridge : qcls (levelRep (n + 1) (-1))
        (goodPlaneEdgeCocycle (edgeParabolic_cycleOpp C primitive hprimitive)) =
        Submodule.Quotient.mk
          (goodPlaneEdgeCocycle (edgeParabolic_cycleOpp C primitive hprimitive)) :=
      rfl
    rw [hbridge, betaZero_mk,
      edgeParabolic_goodPlaneEdgeCocycle_lower_eq_zero C primitive hprimitive]
    simp

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
