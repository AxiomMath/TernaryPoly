module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Final

@[expose] public section


/-!
# The line boundary vector with an arbitrary face scalar (Passage, part D4)

`lineEntryTupleC c f` is the tuple of cusp forms of `Γ₂(N)` with scalar `c` at the good faces (`lineEntryTuple` is `c = (n+1)/2`); `phiLine_eq_lineSeedBoundaryC` is `phiLine_eq_lineSeedBoundary` for it.
This covers the library's section `a_li` (`c = (n+1)/2`) and the paper's good-line section (`c = -(n+1)/2`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.KDaggerComparison (levelN phiLine phiLine_apply phiLineAt)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 fStar)

section

variable {N : ℕ} [NeZero N] {n : ℕ}

open scoped Classical in
/-- The scalar `c` at the faces whose line is good, `0` elsewhere. -/
def lineEntryCoeffC (c : ℂ) (i : LineFaces N) : ℂ := if GoodFlag .line (lineFlagAt i.rep) then c else 0

/-- The tuple of cusp forms of `Γ₂(N)` with scalar `c` at the good faces. -/
def lineEntryTupleC (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    LineFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) :=
  fun i b => if b then levelN N ((starRingEnd ℂ (lineEntryCoeffC c i * (-1) ^ n)) • fStar f)
    else levelN N (lineEntryCoeffC c i • f)

omit [NeZero N] in
theorem lineEntryTuple_eq (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineEntryTuple N n f = lineEntryTupleC (((n : ℂ) + 1) / 2) f := rfl

open scoped Classical in
theorem phiLine_eq_lineSeedBoundaryC (h3 : 3 ∣ N) (hN : 3 ≤ N) (c : ℂ) (a : StratumH2 n trivialCharacter .line)
    (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hbad : ∀ i : LineFaces N, ¬ GoodFlag .line (lineFlagAt i.rep) → phiLineAt N h3 hN n i.rep a = 0)
    (hgood : ∀ i : LineFaces N, GoodFlag .line (lineFlagAt i.rep) →
      phiLineAt N h3 hN n i.rep a = c • ((lineFaceSeedKerClass N n i.rep (levelN N f)).1 +
        (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n i.rep (levelN N (fStar f))).1)) :
    phiLine N h3 hN n a = lineSeedBoundary N n (lineEntryTupleC c f) := by
  ext1 i
  rw [phiLine_apply, lineSeedBoundary_apply]
  have e1 : lineEntryTupleC c f i false = levelN N (lineEntryCoeffC c i • f) := by simp [lineEntryTupleC]
  have e2 : lineEntryTupleC c f i true =
      levelN N ((starRingEnd ℂ (lineEntryCoeffC c i * (-1) ^ n)) • fStar f) := by simp [lineEntryTupleC]
  rw [e1, e2, lineFaceSeedKerClass_levelN_smul, lineFaceSeedConjKerClass_levelN_smul]
  by_cases hg : GoodFlag .line (lineFlagAt i.rep)
  · have hc : lineEntryCoeffC c i = c := ite_eq_left hg
    have hε : (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by push_cast; ring
    rw [hgood i hg, hc, Submodule.coe_smul, Submodule.coe_smul, Complex.conj_conj, hε, smul_add, smul_smul]
  · have hc : lineEntryCoeffC c i = 0 := ite_eq_right hg
    rw [hbad i hg, hc]
    simp

end

end TernaryPeriodPolynomials.Argument.LineSeed
