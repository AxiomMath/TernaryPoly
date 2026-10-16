module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Uniform
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Nonzero
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FaceOrbits
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaces

@[expose] public section


/-!
# The constants of the face factorisation (a′), step (iv)

Formalized by Claude Sonnet 5.5.

Given classes `G o` spanning the cohomology `H³(Stab o.out; ℚ)` of the flag groups (`H3FlagData`, step (ii)) and the sum-zero hypotheses (B_L), (B_P) on the joint restriction images of the line and plane
stabilizers (`LineImageSumZero`, `PlaneImageSumZero`, step (B)), the corner functional `Φ(θ) = θ(pA 3 Ω)` of the Stokes cycle has the same coefficient `Λ = flagLambda0 D` against every `G o`
(`flagPhi_smul`), and `Λ ≠ 0` (`flagLambda0_ne_zero`: the level trace is nonzero and `c₀ ≠ 0`).  The face constants are then `c i = Λ` for lines and `d i = -Λ` for planes
(the plane corner term of the Stokes cycle carries the sign of `PlaneGlue Ψ (-(κ c₀))`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

variable {D : H3FlagData} {F : ConjFrames}

/-- The corner functional on a multiple of the class `G o`. -/
theorem flagPhi_smul (o : labelOrbits Γ6 Flag) (r : ℚ) : flagPhi o (r • D.G o) = r * flagLambda D o := by
  have h : flagPhi o (r • D.G o) = r • flagPhi o (D.G o) := map_smul (flagPhi o) r (D.G o)
  rw [h, smul_eq_mul]
  rfl

/-- **The coefficient of the corner functional against the fundamental classes is nonzero.** -/
theorem flagLambda0_ne_zero (hL : LineImageSumZero D F) (hP : PlaneImageSumZero D F) : flagLambda0 D ≠ 0 := by
  obtain ⟨o, ho⟩ := exists_flagPhi_ne_zero
  rw [← flagLambda_eq_const hL hP o]
  intro h0
  apply ho
  apply LinearMap.ext
  intro y
  obtain ⟨r, rfl⟩ := D.span o y
  have := flagPhi_smul (D := D) o r
  rw [h0, mul_zero] at this
  simpa using this

/-- The constants of the line faces. -/
def lineFaceConst (D : H3FlagData) : TernaryPeriodPolynomials.Argument.GammaNFacesFull.LineFaces 6 → ℂ := fun _ => ((flagLambda0 D : ℚ) : ℂ)

/-- The constants of the plane faces. -/
def planeFaceConst (D : H3FlagData) : TernaryPeriodPolynomials.Argument.SeedC3S4c.PlaneFaces 6 → ℂ := fun _ => -((flagLambda0 D : ℚ) : ℂ)

/-- **Step (iv)**: the constants are all equal to a universal nonzero rational number `Λ` (up to the sign of the planes), and `Λ` is the coefficient of the corner functional of the Stokes cycle against
the fundamental class of every flag group. -/
theorem face_constants (hL : LineImageSumZero D F) (hP : PlaneImageSumZero D F) :
    (∀ i, lineFaceConst D i ≠ 0) ∧ (∀ i, planeFaceConst D i ≠ 0) ∧
      ∃ Λ : ℚ, Λ ≠ 0 ∧ (∀ i, lineFaceConst D i = Λ) ∧ (∀ i, planeFaceConst D i = -Λ) ∧
        ∀ (o : labelOrbits Γ6 Flag) (r : ℚ), flagPhi o (r • D.G o) = Λ * r := by
  have h0 := flagLambda0_ne_zero hL hP
  refine ⟨fun i => ?_, fun i => ?_, flagLambda0 D, h0, fun i => rfl, fun i => rfl, fun o r => ?_⟩
  · simpa [lineFaceConst] using h0
  · simpa [planeFaceConst] using h0
  · rw [flagPhi_smul, flagLambda_eq_const hL hP o, mul_comm]

end TernaryPeriodPolynomials.Argument.GammaNStokes
