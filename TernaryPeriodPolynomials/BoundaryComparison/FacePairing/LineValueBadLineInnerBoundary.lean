module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XInnerBoundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.ParabolicL0
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOdd
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddValueSplit

@[expose] public section


/-!
# The bad-line `lineValue` identity for an `InnerBoundary` line class, reduced to the plane-side
bridge (M4, bad line, step 3, odd degree)

Bad-line analogue of `LineValueGoodLineInnerBoundary.lineValue_goodLine_eq_of_innerBoundary`.
Combines `BadLineFiberOfInnerBoundary.exists_badLineFiber_of_innerBoundary` (M4 step 1) and
`BadXInnerBoundary.badX_mem_parabolicCrossed_of_innerBoundary` (M4 step 2, Hecke-free, explicit
form) with the library's generic bridge theorem
`FiberParabolicL0.lineValue_badLine_parabolicPairing` to compute
`lineValue traceDataL2 ... 0 z w y` as an explicit `parabolicPairing` against the classes of
`badX` and `badXOdd'`, for the *specific* witnesses `z, w, ωU, θU, ...` the caller supplies. This
reduces the gap, for the bad line (odd `n`), to exactly the plane-side membership
`hx'par : badXOdd' hodd hF ∈ parabolicCrossed (levelRep (n + 1) (-1))` — the bad-line analogue of
the good line's own `hx'par` gap.

`hF` and `hxpar` are optional arguments (defaulted to the step-1/step-2 constructions) purely to
keep the statement from repeating their large defining expressions several times over; callers
normally omit both and supply only `hx'par`. The statement is kept at the same level of
abstraction as the good-line template (an explicit `parabolicPairing` against `mkQ`-classes of
`badX`/`badXOdd'`, not the more wrapped `badGoodPairingOdd` form of
`LocalPairingCaseL0OddValueSplit.lineValue_eq_pairing_core`), so that both line formulas can be
summed directly over the same `z, w, y` in the M5 assembly
(`NotBoundaryExactOfLineValueSum.not_boundaryExact_of_lineValue_sum_ne_zero`).
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicPairing twistedPairing_badLine_goodPlane)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd
  (parabolicPairing_congr)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badX badXOdd' levelThreeBridgeBadOdd)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0
  (lineValue_badLine_parabolicPairing)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
  (topVanishing_levelStabilizer)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, bad line, step 3 (odd degree).** For an `InnerBoundary` line coordinate witnessed by
`z, w` and an arbitrary plane class `y`, with the plane-side bridge membership `hx'par` supplied,
`lineValue` at the bad line (`v = 0`) is an explicit nonzero multiple of a `parabolicPairing`.
Composes `lineValue_badLine_parabolicPairing` with
`badX_mem_parabolicCrossed_of_innerBoundary` (M4 step 2, Hecke-free): the gap for the
bad line is exactly the plane-side membership `hx'par`. -/
theorem lineValue_badLine_eq_of_innerBoundary {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
      coordinate)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
        ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀))
    (hF : BadLineFiber n (levelStabilizer e₀) (fun x => z.val.val x L₀)
        (fun x => y.val.val ![(dualityData n trivialCharacter).φ (x 0),
          (dualityData n trivialCharacter).φ (x 1), (dualityData n trivialCharacter).φ (x 2)]
          ((dualityData n trivialCharacter).dualFlag L₀))
        (fun x => w.val x e₀) ωU θU :=
      fiberHyp_line (dualityData n trivialCharacter) endpoint_line_e₀ latL0_le latL0_le_e₀
        z w y hw ωU hωU hdωU θU hθU hdθU)
    (hxpar : badX hn hF ∈ parabolicCrossed (levelRep (n + 1) 0) :=
      badX_mem_parabolicCrossed_of_innerBoundary hn inner z hz w hw y ωU θU hωU hdωU hθU hdθU hF)
    (hx'par : badXOdd' hodd hF ∈ parabolicCrossed (levelRep (n + 1) (-1)))
    (X : parabolicCrossedH1 (levelRep (n + 1) 0))
    (X' : parabolicCrossedH1 (levelRep (n + 1) (-1)))
    (hxcls : (crossedBoundaries (levelRep (n + 1) 0)).mkQ (badX hn hF) = X.1)
    (hx'cls : (crossedBoundaries (levelRep (n + 1) (-1))).mkQ (badXOdd' hodd hF) = X'.1) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (-((n + 1).factorial : ℂ) / 3) *
        parabolicPairing (twistedPairing_badLine_goodPlane hodd) X X' := by
  have h := lineValue_badLine_parabolicPairing (dualityData n trivialCharacter) z w y hw
    (topVanishing_levelStabilizer L₀) ωU hωU hdωU θU hθU hdθU
    (twistedPairing_badLine_goodPlane hodd) hxpar hx'par (levelThreeBridgeBadOdd hodd hF)
  rw [h]
  congr 1
  exact parabolicPairing_congr (twistedPairing_badLine_goodPlane hodd) hxpar hx'par X X' hxcls
    hx'cls

end TernaryPeriodPolynomials.Argument.FacePairing
