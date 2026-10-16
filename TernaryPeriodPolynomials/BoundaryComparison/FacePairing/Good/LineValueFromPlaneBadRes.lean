module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspSeparation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspDualL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Trace

@[expose] public section


/-!
# The good-line local value vanishes for a plane class with zero bad-plane cusp residue

Exact mirror of `BadLineValueFromPlaneGoodRes.lineValue_zero_eq_zero_of_cuspRes_true`, swapping the
roles of the two representative lines of `traceDataL2`: `CuspDualL2.hdual_L2 n χ 1` places the dual
plane of `L₁ = traceDataL2.lineRep 1` in the plane cusp orbit `good 1 = false`, so
`CuspSeparation.fixedPointH2_eq_zero_of_cuspRes` applied with `good := false` kills the good-line
(`v = 1`) term of the `lineValue` sum for any plane class with zero *bad-plane* cusp residue
(`cuspRes _ _ .plane false _ = 0`). Needed for the mirror-image branch of the face-pairing
assembly, where the bad line's cusp residue (rather than the good line's) is the one shown nonzero.
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


/-- **The good-line term of the two-term `lineValue` sum vanishes for a plane class vanishing at the
bad-plane cusp (Hecke-free).** For any plane cocycle `y` whose class has zero bad-plane
(`cuspRes _ _ .plane false _ = 0`) cusp residue, the good-line (`v = 1`) term of the `lineValue` sum
vanishes against any line data `(z, w)` with `w` an `EdgePrimitive` of `z`. Mirror of
`BadLineValueFromPlaneGoodRes.lineValue_zero_eq_zero_of_cuspRes_true`. -/
theorem lineValue_one_eq_zero_of_cuspRes_false (n : ℕ) (χ : RankOneCharacter)
    (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (hw : EdgePrimitive z w)
    (y : MaximalCycles n χ .plane)
    (hbad1 : cuspRes n χ .plane false
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
      0) :
    lineValue traceDataL2 (dualityData n χ) 1 z w y = 0 := by
  have hgood1' : good 1 = false := rfl
  have hF1 : ∃ γ : rationalLevel, γ.val • cuspFlag .plane false =
      (dualityData n χ).dualFlag (traceDataL2.lineRep 1) := by
    rw [← hgood1']
    exact hdual_L2 n χ 1
  have hzero : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      ((dualityData n χ).dualFlag (traceDataL2.lineRep 1))
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
      0 :=
    fixedPointH2_eq_zero_of_cuspRes hF1 hbad1
  obtain ⟨s, hs_eq, hs⟩ := exists_exact_of_fixedPointH2 traceDataL2 (dualityData n χ) 1 y hzero
  exact lineValue_eq_zero_of_exact traceDataL2 (dualityData n χ) 1 hw s hs_eq hs

end TernaryPeriodPolynomials.Argument.FacePairing
