module

public import TernaryPeriodPolynomials.BoundaryComparison.ClassicalFaces.Faces
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntry.Normalization

@[expose] public section


/-!
# Normalization record of the entry certificate

The sign and scalar chain behind `paper_entry_at_classical_faces_of_entry`, each link a proved lemma:

* `entryScalar_rBad_eq_neg_printedScalar`: `entryScalar n S.rBad = -S.printedScalar` (the class-level scalar against the
  library line source is minus the printed scalar), unconditionally;
* `paperLineClass_eq_neg_goodLineClass`: the paper's line section (line seed `σ_h` with the plane-sign datum) is minus
  the class `goodLineClass` of the library line source (`lineSource = -σ_h`), from `classLevel_paper_of_entry`;
* `phiLine_goodLineClass_eq_neg_paperSeed`: `phiLine [goodLineClass] = -(seed vector of scalar -(n+1)/2)`, i.e. the
  `(n+1)/2` seed scalar of the library section against the `-(n+1)/2` of the paper;
* `lineSeedBoundary_lineEntryTupleC_apply_odd`: for odd `n` the face vector is `a • (σ_f - \bar σ_{f*})`, the
  reflection-invariant `ε = +1` combination, so the `(-1)ⁿ` conjugate term carries the minus sign;
* `classical_form_eq_smul_normalized`: the form `f` of the classical seed (`⇑f = classicalFormOfEichlerInput I`) is the
  nonzero scalar `a₁(f)` times the normalized eigenform `S.form` that the finite entry (R2) is computed from.

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.  Reuses `classical_eq_smul_form` and `fourierCoeff_classicalFormOfEichlerInput_one_ne_zero` of
Claude Haiku 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 fStar)
open TernaryPeriodPolynomials.Argument.KDaggerComparison (phiLine goodLineClass levelN)
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.LineSeed
  (lineSeedBoundary lineEntryTupleC lineEntryCoeffC phiLine_goodLineClass_uncond lineFaceSeedKerClass
    lineFaceSeedConjKerClass)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- `entryScalar n S.rBad = -S.printedScalar`, with no hypothesis on the finite entry. -/
theorem entryScalar_rBad_eq_neg_printedScalar {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) :
    entryScalar n S.rBad = -S.printedScalar := by
  rw [S.rBad_eq_rPrint]
  exact S.entryScalar_rPrint

/-- `lineSource = -σ_h` at the level of classes: the paper's line section is minus the good-line class of the
library line source. -/
theorem paperLineClass_eq_neg_goodLineClass (n : ℕ) (D : InducingData n) (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hE : FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad) :
    ∃ hSigP : IsSourceCocycle D .line (fun y g => goodLineWeight g • cSigmaPaper n D S.F y g),
      (SourceQuotient.sourceToSummand D .line
        ⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hSigP⟩).val = -(goodLineClass S I).val := by
  obtain ⟨_, hSigP, _, hNeg⟩ := classLevel_paper_of_entry n D S I hw hv T hT hE
  exact ⟨hSigP, hNeg⟩

/-- The `(n+1)/2` seed scalar of the library section against the `-(n+1)/2` seed scalar of the paper. -/
theorem phiLine_goodLineClass_eq_neg_paperSeed (N : ℕ) [NeZero N] (n : ℕ)
    (hn : Odd n) (h3 : 3 ∣ N) (hN : 3 ≤ N)
    (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I) :
    phiLine N h3 hN n (goodLineClass S I).val =
      -lineSeedBoundary N n (lineEntryTupleC (-(((n : ℂ) + 1) / 2)) f) := by
  rw [lineSeedBoundary_lineEntryTupleC_neg, neg_neg]
  exact phiLine_goodLineClass_uncond hn h3 hN M S I f hf

/-- For odd `n` the face vector of the classical seed is `a • (σ_f - \bar σ_{f*})`: the `(-1)ⁿ` conjugate term is a
minus sign. -/
theorem lineSeedBoundary_lineEntryTupleC_apply_odd (N : ℕ) [NeZero N] (n : ℕ) (hn : Odd n) (c : ℂ)
    (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (i : LineFaces N) :
    lineSeedBoundary N n (lineEntryTupleC c f) i =
      lineEntryCoeffC c i • ((lineFaceSeedKerClass N n i.rep (levelN N f)).1 -
        (lineFaceSeedConjKerClass N n i.rep (levelN N (fStar f))).1) := by
  rw [lineSeedBoundary_lineEntryTupleC_apply, hn.neg_one_pow, mul_neg_one, neg_smul, smul_sub, sub_eq_add_neg]

/-- The form `f` of the classical seed is the nonzero multiple `a₁(f)` of the normalized eigenform `S.form` from which
the finite entry is computed. -/
theorem classical_form_eq_smul_normalized {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I) :
    fourierCoeff (classicalFormOfEichlerInput I) 1 ≠ 0 ∧
      (f : UpperHalfPlane → ℂ) =
        fourierCoeff (classicalFormOfEichlerInput I) 1 • (⇑S.form : UpperHalfPlane → ℂ) :=
  ⟨fourierCoeff_classicalFormOfEichlerInput_one_ne_zero S I hw hv,
    hf.trans ((classicalFormOfEichlerInput_coe I).trans (classical_eq_smul_form S I hw hv))⟩

end TernaryPeriodPolynomials.Argument.BoundaryComparison
