module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineEdgeNonvanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.L0
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Assembly

@[expose] public section


/-!
# A `BadLineFiber` package from an `InnerBoundary` line class and an arbitrary plane class
(M4, bad line, step 1)

Bad-line analogue of `GoodLineFiberOfInnerBoundary.lean`: given an `InnerBoundary` witness for a
line coordinate and *any* plane class `y`, assembles a full `BadLineFiber` package (the fiber
primitives `ωU`/`θU` and the resulting `FiberHyp`) using `exists_omegaU`/`exists_thetaU` fed by
`classOf_lineRestriction_badLine_eq_zero` (via `BadLineEdgeNonvanishing`'s M1 membership step) and
`classOf_planeRestriction_L₀_eq_zero` respectively — no oddness/Hecke hypothesis of any kind
(simpler than the good line, whose own `θU` needs `exists_thetaU_trivial`'s oddness).
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
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipBad
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipPlane
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, bad line, step 1.** From an `InnerBoundary` witness for a line coordinate and an
arbitrary plane class `y`, a `BadLineFiber` package built from the line class's own cocycle
representative `z` and `w`. -/
theorem exists_badLineFiber_of_innerBoundary {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (y : MaximalCycles n trivialCharacter .plane) :
    ∃ (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
        coordinate ∧
      ∃ (_hw : EdgePrimitive z w) (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
        (_hωU : ∀ γ ∈ latL0.sub, ∀ a b,
          ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
        (_hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
        (_hθU : ∀ γ ∈ latL0.sub, ∀ a b,
          θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
            ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
        (_hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
          y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
            (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀)),
        BadLineFiber n (levelStabilizer e₀) (fun x => z.val.val x L₀)
          (fun x => y.val.val ![(dualityData n trivialCharacter).φ (x 0),
            (dualityData n trivialCharacter).φ (x 1), (dualityData n trivialCharacter).φ (x 2)]
            ((dualityData n trivialCharacter).dualFlag L₀))
          (fun x => w.val x e₀) ωU θU := by
  have hrad := cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary inner
  obtain ⟨z, hz, w, hw'⟩ := inner
  have hw : EdgePrimitive z w := fun x e => hw' x e
  obtain ⟨ωU, hωU, hdωU⟩ :=
    exists_omegaU z L₀ latL0.sub latL0_le
      (classOf_lineRestriction_badLine_eq_zero z L₀ rfl latL0.sub latL0_le latL0_mem_rad
        (by rw [hz]; exact hrad))
  obtain ⟨θU, hθU, hdθU⟩ := exists_thetaU (dualityData n trivialCharacter) y L₀ latL0.sub latL0_le
    (classOf_planeRestriction_L₀_eq_zero hn y)
  exact ⟨z, w, hz, hw, ωU, θU, hωU, hdωU, hθU, hdθU,
    fiberHyp_line (dualityData n trivialCharacter) endpoint_line_e₀ latL0_le latL0_le_e₀
      z w y hw ωU hωU hdωU θU hθU hdθU⟩

end TernaryPeriodPolynomials.Argument.FacePairing
