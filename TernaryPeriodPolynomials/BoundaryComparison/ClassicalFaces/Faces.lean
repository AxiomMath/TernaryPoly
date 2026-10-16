module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.TQ
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PerDatumMS
public import TernaryPeriodPolynomials.BoundaryComparison.ClassicalFaces.EntryParam

@[expose] public section


/-!
# The entry certificate at the classical faces, with a supplied finite entry identity

* `paper_entry_at_classical_faces_of_entry` (R3 (b)): the exact type of the argument-flow target
  `paper_entry_at_classical_faces` plus the finite entry identity `hE`, proved from
  `classLevel_paper_of_entry` (scalar `S.printedScalar` against the paper-sign line section, which is minus the
  good-line class) and `LineSeed.phiLine_goodLineClass_uncond` (that class is the classical line-seed boundary vector
  of scalar `(n+1)/2`) and the facewise oddness `lineSeedBoundary_lineEntryTupleC_neg`.  `LineSeed.phiLine_paperLine`
  is deliberately NOT used: its closure contains `entry_dictionary`, hence the old `classLevel_paper` and
  `badPlaneEntryIdentity`.
* The normalization record: `entryScalar n S.rBad = -S.printedScalar`; the paper line section is minus the library line
  source (`goodLineClass`); on the classical faces the scalar `-(n+1)/2` seed vector is minus the scalar `(n+1)/2` one
  (`lineSeedBoundary_lineEntryTupleC_neg`); the antiholomorphic half `(-1)ⁿ conj(.) f*` and the reflection are inside
  `lineEntryTupleC` and `lineSeedBoundary`.
* `goodComponent_line_eq_zero_iff`, `lineSeedBoundary_paper_ne_zero`: the ingredients of the detection through the
  classical faces at `N = 6` (`Certificate.cuspRes_line_true_image_ne_zero_certified`).

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.  Components: `classLevel_paper` (via the entry-parameterized copy) by Claude Sonnet 5.5,
`phiLine_goodLineClass_uncond` by Claude Sonnet 5.5; the composition of the operator
(`Components.lean`) is the preliminary version that uses `phiLine_paperLine`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1)
open TernaryPeriodPolynomials.Argument.KDaggerComparison (phiLine goodLineClass)
open TernaryPeriodPolynomials.Argument.KDaggerComparison (levelN)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (fStar)
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.LineSeed
  (lineSeedBoundary lineEntryTupleC lineEntryCoeffC lineSeedIdentity phiLine_goodLineClass_uncond
    lineSeedBoundary_apply lineFaceSeedKerClass lineFaceSeedConjKerClass lineFaceSeedKerClass_levelN_smul
    lineFaceSeedConjKerClass_levelN_smul)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- Face coefficient of `lineEntryTupleC`: the line seed vector at a face is the holomorphic seed with coefficient
`a` plus the antiholomorphic seed of `f*` with coefficient `a (-1)ⁿ`, where `a` is `c` at good faces and `0` elsewhere. -/
theorem lineSeedBoundary_lineEntryTupleC_apply (N : ℕ) [NeZero N] (n : ℕ) (c : ℂ)
    (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (i : LineFaces N) :
    lineSeedBoundary N n (lineEntryTupleC c f) i =
      lineEntryCoeffC c i • (lineFaceSeedKerClass N n i.rep (levelN N f)).1 +
        (lineEntryCoeffC c i * (-1) ^ n) • (lineFaceSeedConjKerClass N n i.rep (levelN N (fStar f))).1 := by
  rw [lineSeedBoundary_apply]
  have e1 : lineEntryTupleC c f i false = levelN N (lineEntryCoeffC c i • f) := by simp [lineEntryTupleC]
  have e2 : lineEntryTupleC c f i true =
      levelN N ((starRingEnd ℂ (lineEntryCoeffC c i * (-1) ^ n)) • fStar f) := by simp [lineEntryTupleC]
  rw [e1, e2, lineFaceSeedKerClass_levelN_smul, lineFaceSeedConjKerClass_levelN_smul, Complex.conj_conj,
    Submodule.coe_smul, Submodule.coe_smul]

/-- **Sign chain 3 (the `-(n+1)/2` seed scalar), facewise.**  The classical line-seed vector is odd in the scalar `c`:
at each face the holomorphic coefficient is `-a` and the antiholomorphic one `-a (-1)ⁿ` (the conjugate of the real-sign
change `-1` is `-1`, so the `(-1)ⁿ` conjugate term changes sign with `c`).  Pure consequence of
`lineFaceSeedKerClass_levelN_smul` and `lineFaceSeedConjKerClass_levelN_smul`; no entry or dictionary input. -/
theorem lineSeedBoundary_lineEntryTupleC_neg (N : ℕ) [NeZero N] (n : ℕ) (c : ℂ)
    (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineSeedBoundary N n (lineEntryTupleC (-c) f) = -lineSeedBoundary N n (lineEntryTupleC c f) := by
  ext1 i
  rw [DFinsupp.neg_apply, lineSeedBoundary_lineEntryTupleC_apply, lineSeedBoundary_lineEntryTupleC_apply]
  have hcoef : lineEntryCoeffC (-c) i = -lineEntryCoeffC c i := by
    unfold lineEntryCoeffC
    split_ifs <;> simp
  rw [hcoef, neg_mul, neg_smul, neg_smul, neg_add]

/-- **R3 (b).**  The exact type of `paper_entry_at_classical_faces` (argument-flow target), with the finite entry
identity `hE` as an explicit input in place of `badPlaneEntryIdentity S`.

Proof (no use of `phiLine_paperLine`, `paperLineSeedIdentity` or `entry_dictionary`, whose closures contain the
old `classLevel_paper`/`badPlaneEntryIdentity`): `classLevel_paper_of_entry` gives
`goodComponent (T ζ) = S.printedScalar • [paper line section]` and `[paper line section] = -[goodLineClass]`;
`phiLine_goodLineClass_uncond` (from `lineSeedIdentity`, i.e. the line edge and the ordinary Eichler period calculus)
gives `phiLine [goodLineClass] = lineSeedBoundary (lineEntryTupleC ((n+1)/2) f)`; and
`lineSeedBoundary_lineEntryTupleC_neg` turns the sign into the scalar `-(n+1)/2`.  The scalar is the L-series scalar
`S.printedScalar`; the seed is the classical line seed of `f` (`⇑f = classicalFormOfEichlerInput I`) including the
`(-1)ⁿ` antiholomorphic half. -/
theorem paper_entry_at_classical_faces_of_entry (N : ℕ) [NeZero N] (n : ℕ)
    (hn : Odd n) (h3 : 3 ∣ N) (hN : 3 ≤ N)
    (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand M.inducingData .plane →ₗ[ℂ] boundarySummand M.inducingData .line)
    (hT : RealizesStandardConv M.inducingData T)
    (hE : FiniteEntryIdentity M.inducingData badPlaneWeight goodLineWeight S.F S.rBad) :
    phiLine N h3 hN n
        (goodComponent n M.inducingData.chi .line
          (T (SphericalEntryData.badPlaneClass S I)).val) =
      S.printedScalar • lineSeedBoundary N n
        (lineEntryTupleC (-(((n : ℂ) + 1) / 2)) f) := by
  have hobtain1 := classLevel_paper_of_entry n M.inducingData S I hw hv T hT hE
  obtain ⟨_, hLP, hentry, hNeg⟩ := hobtain1
  have h2 : phiLine N h3 hN n (goodLineClass S I).val =
      lineSeedBoundary N n (lineEntryTupleC (((n : ℂ) + 1) / 2) f) :=
    phiLine_goodLineClass_uncond hn h3 hN M S I f hf
  have hP : phiLine N h3 hN n (SourceQuotient.sourceToSummand M.inducingData .line
        ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val =
      lineSeedBoundary N n (lineEntryTupleC (-(((n : ℂ) + 1) / 2)) f) := by
    exact (congrArg (phiLine N h3 hN n) hNeg).trans ((map_neg (phiLine N h3 hN n) _).trans
      ((congrArg Neg.neg h2).trans (lineSeedBoundary_lineEntryTupleC_neg N n _ f).symm))
  exact (congrArg (phiLine N h3 hN n) hentry).trans
    ((map_smul (phiLine N h3 hN n) S.printedScalar _).trans (congrArg (S.printedScalar • ·) hP))

/-! ### Normalization record -/

/-- Sign chain 1: the class-level scalar against the library line source is minus the printed scalar. -/
theorem entryScalar_eq_neg_printedScalar_of_entry (n : ℕ) (D : InducingData n) (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hE : FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad) :
    entryScalar n S.rBad = -S.printedScalar :=
  (classLevel_badPlane_eichler_of_entry n D S I hw hv T hT hE).2.1

/-! ### Detection through the classical faces -/

/-- The good-line component of a line class vanishes iff its coordinate at the good-line cusp does. -/
theorem goodComponent_line_eq_zero_iff {n : ℕ} {χ : RankOneCharacter} (a : StratumH2 n χ .line) :
    goodComponent n χ .line a = 0 ↔ cuspRes n χ .line true a = 0 := by
  constructor
  · intro h
    rw [← cuspRes_goodComponent, h, map_zero]
  · intro h
    refine (eq_zero_iff_cuspRes .line _).mpr ⟨by rw [cuspRes_goodComponent]; exact h, ?_⟩
    unfold goodComponent
    rw [cuspRes_flagProj]
    have hw : goodWeight .line (cuspFlag .line false) = 0 := by
      unfold goodWeight
      rw [ite_eq_right]
      intro hg
      exact absurd ((cuspFlag_good_iff .line false).mp hg) (by simp)
    rw [hw, zero_smul]

/-- The classical line-seed vector (scalar `-(n+1)/2`) of the form of an Eichler input is nonzero.

**Limitation.** The line-seed nonvanishing is derived from the level-one Eichler-Shimura nonvanishing of the line
source (`lineSource_cuspRes_ne_zero_of_eichler`), not from an independent `Γ(N)` line-seed injectivity theorem (the
library's `seedMapInjective` is a statement about plane faces; no line-face analogue exists).

Derivation: the vector is minus `phiLine` of the good-line class of the Eichler line source
(`lineSeedBoundary_lineEntryTupleC_neg`, `phiLine_goodLineClass_uncond`), `phiLine` is injective
(`eq_zero_of_phiLine_eq_zero`), and that class has nonzero coordinate at the good-line cusp.  No entry identity and no
`classLevel_paper` is involved. -/
theorem lineSeedBoundary_paper_ne_zero (N : ℕ) [NeZero N] (n : ℕ)
    (hn : Odd n) (h3 : 3 ∣ N) (hN : 3 ≤ N)
    (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I) :
    lineSeedBoundary N n (lineEntryTupleC (-(((n : ℂ) + 1) / 2)) f) ≠ 0 := by
  have h2 : phiLine N h3 hN n (goodLineClass S I).val =
      lineSeedBoundary N n (lineEntryTupleC (((n : ℂ) + 1) / 2) f) :=
    phiLine_goodLineClass_uncond hn h3 hN M S I f hf
  intro h0
  rw [lineSeedBoundary_lineEntryTupleC_neg, neg_eq_zero, ← h2] at h0
  have hL : (goodLineClass S I).val = 0 :=
    TernaryPeriodPolynomials.Argument.KDaggerComparison.eq_zero_of_phiLine_eq_zero N h3 hN n _ h0
  have hls0 : IsSourceCocycle M.inducingData .line (lineSource M.inducingData (SphericalEntryData.lineLevi I)) :=
    lineSource_isSourceCocycle M.inducingData _ S.hχ
  have hline_ne := lineSource_cuspRes_ne_zero_of_eichler M.inducingData rfl I hn hls0
  have hgood : cuspRes n M.inducingData.chi .line true (goodLineClass S I).val ≠ 0 := by
    have e : (goodLineClass S I).val = SourceSpace.sourceClass M.inducingData .line
        ⟨fun y g => goodLineWeight g • lineSource M.inducingData (SphericalEntryData.lineLevi I) y g,
          SphericalEntryData.goodLine_isSourceCocycle S I⟩ := rfl
    rw [e, cuspRes_line_true_goodLine M.inducingData _ hls0]
    exact hline_ne
  exact hgood (by rw [hL, map_zero])

end TernaryPeriodPolynomials.Argument.BoundaryComparison
