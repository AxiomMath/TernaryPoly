module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspSeparation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspDualL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Trace

@[expose] public section


/-!
# The bad-line local value vanishes for a plane class with zero good-plane cusp residue

(M4, killing the bad-line term of the two-term `lineValue` sum; Hecke-free.)

`CuspSeparation.lean`'s generic cusp-separation machinery
(`fixedPointH2_eq_zero_of_cuspRes`, `exists_exact_of_fixedPointH2`, `lineValue_eq_zero_of_exact`)
already supplies, for *any* plane cocycle class vanishing at a given plane cusp orbit, a vanishing
`lineValue` term at any representative line whose dual plane lies in that same orbit. Combined with
`CuspDualL2.hdual_L2` — the boundary trace's own cusp data, confirming the dual plane of the base
line `L₀ = traceDataL2.lineRep 0` lies in the *good* plane cusp orbit (`CuspDualL2.good 0 = true`,
`CuspDualL2.lineRep_zero`) — this kills the bad-line (`v = 0`) term of the two-term `lineValue` sum
for any plane class with zero *good-plane* cusp residue (`cuspRes _ _ .plane true _ = 0`).

This is exactly the property already carried by the plane witness that
`GoodPlaneSpan.GoodFlagTransport.vanishesOnGood_of_cuspRes_good_eq_zero` and
`BridgeXPrimeInnerBoundary.bridgeX'_mem_parabolicCocycles_of_innerBoundary`'s own `hgood` hypothesis
need for the good-line (`v = 1`) nonvanishing argument (`PlanePeriodParabolicRealized`'s witness `b`
comes with `cuspRes n trivialCharacter .plane true b = 0` built in, per `CuspidalSpan/OddCase.lean`)
— so the *same* plane witness used for the good-line nonvanishing half automatically kills the
bad-line term too, with no separate construction (in particular, no Shapiro-seeding) needed.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (hdual_L2 good)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers (fixedPointH2)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **The bad-line term of the two-term `lineValue` sum vanishes for a plane class vanishing at the
good-plane cusp (Hecke-free).** For any plane cocycle `y` whose class has zero good-plane
(`cuspRes _ _ .plane true _ = 0`) cusp residue, the bad-line (`v = 0`) term of the `lineValue` sum
vanishes against any line data `(z, w)` with `w` an `EdgePrimitive` of `z`. -/
theorem lineValue_zero_eq_zero_of_cuspRes_true (n : ℕ) (χ : RankOneCharacter)
    (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (hw : EdgePrimitive z w)
    (y : MaximalCycles n χ .plane)
    (hgood0 : cuspRes n χ .plane true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
      0) :
    lineValue traceDataL2 (dualityData n χ) 0 z w y = 0 := by
  have hgood0' : good 0 = true := rfl
  have hF0 : ∃ γ : rationalLevel, γ.val • cuspFlag .plane true =
      (dualityData n χ).dualFlag (traceDataL2.lineRep 0) := by
    rw [← hgood0']
    exact hdual_L2 n χ 0
  have hzero : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      ((dualityData n χ).dualFlag (traceDataL2.lineRep 0))
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
      0 :=
    fixedPointH2_eq_zero_of_cuspRes hF0 hgood0
  obtain ⟨s, hs_eq, hs⟩ := exists_exact_of_fixedPointH2 traceDataL2 (dualityData n χ) 0 y hzero
  exact lineValue_eq_zero_of_exact traceDataL2 (dualityData n χ) 0 hw s hs_eq hs

end TernaryPeriodPolynomials.Argument.FacePairing
