module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ParityCases
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge

@[expose] public section


/-!
# A line class with nonzero coordinate at the good line forces sphericity

In `LocalNondegenerate` at the line cusp `v = 1` the line summand class `b` has nonzero Shapiro
coordinate at the representative line `L₁`, a translate of the reference good line. Hence
the line coordinate image at the good line is nonzero, so `D.cusp` has a `GL₂(ℤ̂)`-fixed vector.
This is the only input from the line side needed to identify the joint generalized eigenspace of
the prime operators `T_p` with the full local joint eigenspace at the dual identity plane
(`HeckeGenEqIdentity`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq

open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
open TernaryPeriodPolynomials.BoundaryDuality.ParityCases
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-- **A line summand class with nonzero coordinate at the representative good line `L₁` gives a
nonzero line coordinate image at the good line cusp.** -/
theorem coordinateImage_line_true_ne_bot_of_lineRep_one {D : InducingData n}
    {b : StratumH2 n D.chi .line} (hb : b ∈ boundarySummand D .line)
    (hne : fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
      (traceDataL2.lineRep 1) b ≠ 0) :
    coordinateImage D .line true ≠ ⊥ := by
  intro hbot
  apply hne
  have hmem : cuspRes n D.chi .line true b ∈ coordinateImage D .line true := ⟨b, hb, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact fixedPointH2_eq_zero_of_cuspRes_side goodLine_orbit hmem

/-- **A line summand class with nonzero coordinate at `L₁` forces sphericity of `D.cusp`.** -/
theorem sphericalCusp_of_lineRep_one {D : InducingData n} {b : StratumH2 n D.chi .line}
    (hb : b ∈ boundarySummand D .line)
    (hne : fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
      (traceDataL2.lineRep 1) b ≠ 0) : SphericalCusp D.cusp :=
  sphericalCusp_of_coordinateImage_line_ne_bot D
    (coordinateImage_line_true_ne_bot_of_lineRep_one hb hne)

end TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq
