module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineEdgeInnerIdentification
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.L0

@[expose] public section


/-!
# `badX`'s parabolicity from an `InnerBoundary` line class (M4, bad line, step 2)

Combines the fiber package from `BadLineFiberOfInnerBoundary` (step 1) with the identification
`BadLineEdgeInnerIdentification.badLineEdge_cuspRes_eq_innerBadLineArithmeticBinaryMap` (step 2a)
through the generic bridge `BadIdentLine.mkQ_badX_eq_neg_badLineEdge_cusp`, mirroring exactly the
Hecke-dependent proof of `BadIdentLine.badX_mem_parabolicCrossed` but substituting the Hecke-free
parabolicity obtained from an `InnerBoundary` witness for the Hecke-eigenspace membership that
theorem uses instead.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, bad line, step 2.** From an `InnerBoundary` witness for a line coordinate and an
arbitrary plane class `y`, a `badX` term that is parabolic — Hecke-free, built from the fiber
package of `exists_badLineFiber_of_innerBoundary` and the identification
`badLineEdge_cuspRes_eq_innerBadLineArithmeticBinaryMap`. -/
theorem exists_badX_mem_parabolicCrossed_of_innerBoundary {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (y : MaximalCycles n trivialCharacter .plane) :
    ∃ (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
      (_hw : EdgePrimitive z w) (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
      (hF : BadLineFiber n (levelStabilizer e₀) (fun x => z.val.val x L₀)
        (fun x => y.val.val ![(dualityData n trivialCharacter).φ (x 0),
          (dualityData n trivialCharacter).φ (x 1), (dualityData n trivialCharacter).φ (x 2)]
          ((dualityData n trivialCharacter).dualFlag L₀))
        (fun x => w.val x e₀) ωU θU),
      badX hn hF ∈ parabolicCrossed (binaryArithmeticRepresentation n) := by
  obtain ⟨z, w, hz, hw, ωU, θU, hωU, hdωU, hθU, hdθU, hF⟩ :=
    exists_badLineFiber_of_innerBoundary hn inner y
  refine ⟨z, w, hw, ωU, θU, hF, ?_⟩
  apply mem_parabolicCrossed_of_mem
  rw [mkQ_badX_eq_neg_badLineEdge_cusp hn hF z (fun _ => rfl)]
  obtain ⟨aBad, heq, hpar⟩ := badLineEdge_cuspRes_eq_innerBadLineArithmeticBinaryMap hn inner
    (cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner)
  have hpoint : (⟨cuspRes n trivialCharacter .line false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z),
      classOf_mem_kernel hF (cocycleAtBadLine n z) (zeta_eq_cocycleAtBadLine n z (fun _ => rfl))⟩ :
      badLineLocalRadicalKernel n) =
      ⟨cuspRes n trivialCharacter .line false coordinate,
        cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner⟩ :=
    Subtype.ext (congrArg (cuspRes n trivialCharacter .line false) hz)
  rw [hpoint, heq]
  exact Submodule.neg_mem _ hpar

/-- **M4, bad line, step 2 (explicit form).** `badX` is a parabolic cocycle for an `InnerBoundary`
line class, with explicit witnesses `z, w` for the line class and an explicit plane class `y` —
the explicit-argument companion to `exists_badX_mem_parabolicCrossed_of_innerBoundary`, matching
the good line's `BridgeXInnerBoundary.bridgeX_mem_parabolicCocycles_of_innerBoundary` in shape, for
direct use as a defaulted argument in the value formula (M4 step 3). -/
theorem badX_mem_parabolicCrossed_of_innerBoundary {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
      coordinate)
    (w : EdgeCochains n trivialCharacter 1) (hw : EdgePrimitive z w)
    (y : MaximalCycles n trivialCharacter .plane)
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
        z w y hw ωU hωU hdωU θU hθU hdθU) :
    badX hn hF ∈ parabolicCrossed (binaryArithmeticRepresentation n) := by
  apply mem_parabolicCrossed_of_mem
  rw [mkQ_badX_eq_neg_badLineEdge_cusp hn hF z (fun _ => rfl)]
  obtain ⟨aBad, heq, hpar⟩ := badLineEdge_cuspRes_eq_innerBadLineArithmeticBinaryMap hn inner
    (cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner)
  have hpoint : (⟨cuspRes n trivialCharacter .line false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z),
      classOf_mem_kernel hF (cocycleAtBadLine n z) (zeta_eq_cocycleAtBadLine n z (fun _ => rfl))⟩ :
      badLineLocalRadicalKernel n) =
      ⟨cuspRes n trivialCharacter .line false coordinate,
        cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner⟩ :=
    Subtype.ext (congrArg (cuspRes n trivialCharacter .line false) hz)
  rw [hpoint, heq]
  exact Submodule.neg_mem _ hpar

end TernaryPeriodPolynomials.Argument.FacePairing
