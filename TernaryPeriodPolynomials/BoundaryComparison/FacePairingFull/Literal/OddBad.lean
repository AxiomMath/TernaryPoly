module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.LineValueBadLineInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.XPrimeInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.Even

@[expose] public section


/-!
# Value formula at the bad line for arbitrary inner classes: odd `n`

For odd `n > 0` and inner classes `b` (line), `ξ` (plane),
`lineValue 0 z w y = (-(n+1)!/3) · badGoodPairingOdd (badLineParabolic b) (goodPlaneParabolic ξ)` for
all representatives (`lineValue_zero_odd`): the library bridge theorem
`LineValueBadLineInnerBoundary.lineValue_badLine_eq_of_innerBoundary`, with the classes of the bridge
cocycles identified with the dictionary (`mkQ_badXOdd'_eq_thetaPar`, `mkQ_badX_eq_badLineParabolic`) and
moved to arbitrary representatives by local independence.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badX badXOdd' levelThreeBridgeBadOdd)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd
  (qcls_badXOdd'_eq mkQ_eq_qcls thetaPar badGoodPairingOdd)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

section Generic

variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

theorem mkQ_badXOdd'_eq_thetaPar (hn : 0 < n) (hodd : Odd n)
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (ξ : innerClasses n .plane)
    (y : MaximalCycles n trivialCharacter .plane)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val) :
    (crossedBoundaries (levelRep (n + 1) (-1))).mkQ (badXOdd' hodd hF) =
      ((thetaPar hodd (goodPlaneParabolic hn ξ) :
        parabolicCrossedH1 (levelRep (n + 1) (-1))) : CrossedH1 (levelRep (n + 1) (-1))) := by
  have e := LocalPairingCaseL0Odd.thetaPar_coe hodd (goodPlaneParabolic hn ξ)
  rw [e, goodPlaneParabolic_coe hn ξ _ hy, mkQ_eq_qcls, qcls_badXOdd'_eq hodd hn hF y hη]

end Generic

theorem lineValue_zero_odd {n : ℕ} (hn : 0 < n) (hodd : Odd n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (flat : PlaneEdgeExact y) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (-((n + 1).factorial : ℂ) / 3) *
        badGoodPairingOdd hodd (badLineParabolic hn b) (goodPlaneParabolic hn ξ) := by
  have hbin : InnerBoundary n trivialCharacter .line b.val := b.property
  obtain ⟨z₂, w₂, hz₂, hw₂, ωU, θU, hωU, hdωU, hθU, hdθU, hF⟩ :=
    exists_badLineFiber_of_innerBoundary hn hbin y
  have hinner_y : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) := by
    rw [hy]; exact ξ.property
  have hinner_z : InnerBoundary n trivialCharacter .line
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₂) := by
    rw [hz₂]; exact hbin
  have hxpar := badX_mem_parabolicCrossed_of_innerBoundary hn hbin z₂ hz₂ w₂ hw₂ y ωU θU hωU hdωU
    hθU hdθU
  have hx'par := badXOdd'_mem_parabolicCrossed_of_innerBoundary hn hodd z₂ w₂ hw₂ y ωU θU hωU
    hdωU hθU hdθU hinner_y
  have hη' := hη_flag
    (η := fun x => y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀)) y (fun _ => rfl)
  have hxcls := mkQ_badX_eq_badLineParabolic hn hF b z₂ (fun _ => rfl) hz₂ hinner_z
  have hx'cls := mkQ_badXOdd'_eq_thetaPar hn hodd hF ξ y hη' hy
  have h1 := lineValue_badLine_eq_of_innerBoundary hn hodd hbin z₂ w₂ hz₂ hw₂ y ωU θU hωU hdωU
    hθU hdθU (hF := hF) (hxpar := hxpar) (hx'par := hx'par) (X := badLineParabolic hn b)
    (X' := thetaPar hodd (goodPlaneParabolic hn ξ)) (hxcls := hxcls) (hx'cls := hx'cls)
  have h2 := LocalIndependence.lineValue_eq_of_line_fixedPointH2_eq traceDataL2
    (dualityData n trivialCharacter) 0 hw hw₂ flat
    (congrArg (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (traceDataL2.lineRep 0)) (hz.trans hz₂.symm))
  exact h2.trans h1

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
