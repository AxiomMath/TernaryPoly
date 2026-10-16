module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.FlagReal
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Values
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# The flag constant terms `r_B = 0` of the series and of the dual series, unconditional

Formalized by Claude Sonnet 5.5.

* `series_plane_cuspidal`: for `3 ≤ N`, `4 ≤ n`, the complexified plane restriction at EVERY plane cusp `k⁻¹Pk` of the series at ANY cusp `h'` (either seed) is mixed cuspidal: by the exact
  values it lies in the span of the seed classes (`TernaryPeriodPolynomials.Argument.FormClassK.cuspValues`, field `mem`), and `faceSeedSpan_le_cuspidalInH2`;
* `series_rB_zero`: `r_B ℰ_P = 0` on `Γ(N) ∩ h⁻¹Bh` for every `h` (every flag group arises this way), real coefficients (`FlagReal.resTo_gammaNBAt_zero_of_cuspidal`);
* `dual_rB_zero`: `r_B ℰ_Q^∨ = 0` on `Γ(N) ∩ h⁻¹Bh` for every `h`, both seeds, every cusp `h'` of the dual series (`FlagReal.dual_rB_zero_of_cuspidal`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The complexified plane restriction of the series at any cusp is mixed cuspidal at every plane cusp.** -/
theorem series_plane_cuspidal (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) (h' k : SL(3, ℤ)) :
    complexifyAt N k n (resTo (gammaNPAt N k) (gammaNPAt_le N k) (gammaRho (gammaN N) n)
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f h' b hn)) ∈ faceCuspidalInH2 N k n := by
  have e : complexifyAt N k n (resTo (gammaNPAt N k) (gammaNPAt_le N k) (gammaRho (gammaN N) n)
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f h' b hn)) =
      TernaryPeriodPolynomials.Argument.FormClassK.resAtC N k n (EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f h' b hn)) :=
    (resAtC_complexify N k n _).symm
  rw [e]
  exact TernaryPeriodPolynomials.Argument.FormClassK.faceSeedSpan_le_cuspidalInH2 N k n
    ((TernaryPeriodPolynomials.Argument.FormClassK.cuspValues N n hN hn).mem f k h' b)

/-- **`r_B ℰ_P = 0` at every flag group `Γ(N) ∩ h⁻¹Bh`**, for the series at any cusp and either seed (unconditional). -/
theorem series_rB_zero (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) (h' h : SL(3, ℤ)) :
    resTo (gammaNBAt N h) (gammaNBAt_le_N N h) (gammaRho (gammaN N) n)
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f h' b hn) = 0 :=
  resTo_gammaNBAt_zero_of_cuspidal N n h hN _ (series_plane_cuspidal N n f hN hn b h' h)

/-- **`r_B ℰ_Q^∨ = 0` at every flag group `Γ(N) ∩ h⁻¹Bh`** for the dual series at any line cusp and either seed (unconditional; `3 ≤ N`, `4 ≤ n`). -/
theorem dual_rB_zero (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) (h' h : SL(3, ℤ)) :
    resTo (gammaNBAt N h) (gammaNBAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn b h') = 0 := by
  rw [dualSeriesAtClass_gammaN_eq]
  exact dual_rB_zero_of_cuspidal N n hN _ h
    (series_plane_cuspidal N n f hN hn b (jmath h') (jmath h))

end TernaryPeriodPolynomials.Argument.EisensteinDual
