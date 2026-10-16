module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.KLMembership
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.PsiLReconciliation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipGood
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.L1
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1TrivialValue

@[expose] public section


/-!
# A `GoodLineFiber` package from an `InnerBoundary` line class and an arbitrary plane class
(M4, good line, step 1)

Given `coordinate : StratumH2 n trivialCharacter .line` with an `InnerBoundary` witness, and an
*arbitrary* plane class `y`, this builds the `GoodLineFiber` hypothesis `fiberHyp_goodLine`
(`FiberL1.lean`) needs, using:

* the line `U`-primitive `ωU` from `FiberExact.exists_omegaU`, fed by the vanishing
  `HeckeAdjointMembershipGood.classOf_lineRestriction_goodLine_eq_zero`, whose own hypothesis
  `hML : cuspRes n trivialCharacter .line true (classOf ... z) ∈ LocalUniqueness.ML n` is built
  *directly* from `KLMembership.fixedPointH2_mem_KL_of_innerBoundary` and
  `PsiLReconciliation.psiL_cuspRes_eq` — **no `localJoint`/Hecke-eigenspace reasoning is used**,
  unlike `LocalPairingCaseL1TrivialValue.exists_omegaU_trivial`, which packages the same
  construction behind a `localJoint` hypothesis for a different call site;
* the dual plane `U`-primitive `θU` from the unconditional
  `LocalPairingCaseL1Trivial.exists_thetaU_trivial`.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₂ L₁)
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipGood
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, good line, step 1.** Packages a `GoodLineFiber` hypothesis from an `InnerBoundary` line
class and an arbitrary plane class `y`. -/
theorem exists_goodLineFiber_of_innerBoundary {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (y : MaximalCycles n trivialCharacter .plane) :
    ∃ (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1),
      classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
        coordinate ∧
      ∃ (_hw : EdgePrimitive z w) (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
        (_hωU : ∀ γ ∈ latL1.sub, ∀ a b,
          ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
        (_hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
        (_hθU : ∀ γ ∈ latL1.sub, ∀ a b,
          θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
            ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
        (_hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
          y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
            (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₁)),
        GoodLineFiber n trivialCharacter (levelStabilizer e₂) (lineCocycle z)
          (planeCocycle (dualityData n trivialCharacter) y) (edgeCochain w) ωU θU := by
  have hKL := fixedPointH2_mem_KL_of_innerBoundary inner
  obtain ⟨z, hz, w, hw'⟩ := inner
  have hw : EdgePrimitive z w := fun x e => hw' x e
  have hML : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
      ML n := by
    rw [Submodule.mem_comap, hz, psiL_cuspRes_eq]
    exact hKL
  obtain ⟨ωU, hωU, hdωU⟩ :=
    exists_omegaU z L₁ latL1.sub latL1_le
      (classOf_lineRestriction_goodLine_eq_zero z L₁
        TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident.L₁_eq_goodLine
        latL1.sub latL1_le latL1_mem_rad hML)
  obtain ⟨θU, hθU, hdθU⟩ := exists_thetaU_trivial hn hodd y
  exact ⟨z, w, hz, hw, ωU, θU, hωU, hdωU, hθU, hdθU,
    fiberHyp_goodLine (dualityData n trivialCharacter) z w y hw ωU hωU hdωU θU hθU hdθU⟩

end TernaryPeriodPolynomials.Argument.FacePairing
