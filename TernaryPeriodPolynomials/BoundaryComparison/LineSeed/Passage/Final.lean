module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Lin
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Vanish
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge5

@[expose] public section


/-!
# The line boundary vector of the entry section (Passage, part D3)

`lineEntryTuple f` is the tuple of cusp forms of `Γ₂(N)` attached to the entry section `a_li`: at a face `i` whose line flag is good, `κ • f|Γ₂(N)` (holomorphic seed) and `conj(κ (-1)ⁿ) • f*|Γ₂(N)`
(antiholomorphic seed), `κ = (n+1)/2` (`lineEntryCoeff`); at the other faces `0`.  `phiLine_eq_lineSeedBoundary`: a stratum class whose coordinate is `κ (seedKer f + (-1)ⁿ seedConjKer f*)` at the good
faces and zero at the non-good faces has `phiLine a = lineSeedBoundary (lineEntryTuple f)`.  The non-good faces are discharged by `phiLineAt_goodLineClass_bad`; the good faces by the per-face theorem.

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
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.EntryDictionary
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Argument.KDaggerComparison (goodLineClass)

section

variable (N : ℕ) [NeZero N] (n : ℕ)

open scoped Classical in
/-- The scalar of the face `i`: `(n+1)/2` at the faces whose line is good, `0` elsewhere. -/
def lineEntryCoeff (i : LineFaces N) : ℂ :=
  if GoodFlag .line (lineFlagAt i.rep) then ((n : ℂ) + 1) / 2 else 0

/-- **The tuple of cusp forms of `Γ₂(N)` attached to the entry section `a_li`.** -/
def lineEntryTuple (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    LineFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) :=
  fun i b => if b then levelN N ((starRingEnd ℂ (lineEntryCoeff N n i * (-1) ^ n)) • fStar f)
    else levelN N (lineEntryCoeff N n i • f)

variable {N n}

theorem lineFaceSeedKerClass_levelN_zero (h : SL(3, ℤ)) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineFaceSeedKerClass N n h (levelN N ((0 : ℂ) • f)) = 0 := by
  rw [lineFaceSeedKerClass_levelN_smul, zero_smul]

theorem lineFaceSeedConjKerClass_levelN_zero (h : SL(3, ℤ)) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineFaceSeedConjKerClass N n h (levelN N ((0 : ℂ) • f)) = 0 := by
  rw [lineFaceSeedConjKerClass_levelN_smul, map_zero, zero_smul]

open scoped Classical in
/-- **The line boundary vector of the entry section.** -/
theorem phiLine_eq_lineSeedBoundary (h3 : 3 ∣ N) (hN : 3 ≤ N) (a : StratumH2 n trivialCharacter .line)
    (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hbad : ∀ i : LineFaces N, ¬ GoodFlag .line (lineFlagAt i.rep) → phiLineAt N h3 hN n i.rep a = 0)
    (hgood : ∀ i : LineFaces N, GoodFlag .line (lineFlagAt i.rep) →
      phiLineAt N h3 hN n i.rep a = (((n : ℂ) + 1) / 2) • ((lineFaceSeedKerClass N n i.rep (levelN N f)).1 +
        (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n i.rep (levelN N (fStar f))).1)) :
    phiLine N h3 hN n a = lineSeedBoundary N n (lineEntryTuple N n f) := by
  ext1 i
  rw [phiLine_apply, lineSeedBoundary_apply]
  have e1 : lineEntryTuple N n f i false = levelN N (lineEntryCoeff N n i • f) := by simp [lineEntryTuple]
  have e2 : lineEntryTuple N n f i true =
      levelN N ((starRingEnd ℂ (lineEntryCoeff N n i * (-1) ^ n)) • fStar f) := by simp [lineEntryTuple]
  rw [e1, e2, lineFaceSeedKerClass_levelN_smul, lineFaceSeedConjKerClass_levelN_smul]
  by_cases hg : GoodFlag .line (lineFlagAt i.rep)
  · have hc : lineEntryCoeff N n i = ((n : ℂ) + 1) / 2 := ite_eq_left hg
    have hε : (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by push_cast; ring
    rw [hgood i hg, hc, Submodule.coe_smul, Submodule.coe_smul, Complex.conj_conj, hε, smul_add, smul_smul]
  · have hc : lineEntryCoeff N n i = 0 := ite_eq_right hg
    rw [hbad i hg, hc]
    simp

/-- **The line boundary vector of the entry section `a_li`** (conditional on the per-face seed theorem at the good faces): `phiLine a_li = lineSeedBoundary (lineEntryTuple f)`. -/
theorem phiLine_goodLineClass (h3 : 3 ∣ N) (hN : 3 ≤ N) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hgood : ∀ i : LineFaces N, GoodFlag .line (lineFlagAt i.rep) →
      phiLineAt N h3 hN n i.rep (goodLineClass S I).val = (((n : ℂ) + 1) / 2) •
        ((lineFaceSeedKerClass N n i.rep (levelN N f)).1 +
          (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n i.rep (levelN N (fStar f))).1)) :
    phiLine N h3 hN n (goodLineClass S I).val = lineSeedBoundary N n (lineEntryTuple N n f) :=
  phiLine_eq_lineSeedBoundary h3 hN _ f (fun i hb => phiLineAt_goodLineClass_bad N h3 hN M S I i.rep hb) hgood

end

end TernaryPeriodPolynomials.Argument.LineSeed
