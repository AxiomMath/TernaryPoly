module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PerDatumMS
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.sStd.StandardFromT0
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison

@[expose] public section


/-!
# The class-level entry identity for the paper's actual constant-term map `T₀`

`Entry.classLevel_paper` is stated for any `T` realizing the standard operator.  Here `T` is the restriction of the
constant-term map `T₀ := (line_constant_term_comparison n hn).choose` of Proposition C.5 (the map of the target, characterised by its
uniqueness clause `IsUniquenessMap`) to the summands of `D`, `ConsumersStd.standardFromT0Std`; its hypotheses are
discharged for the actual family: the plane Eisenstein hypothesis is `planeEisensteinConvergent` (absolute convergence,
`n ≥ 4`), `hT₀` is `(line_constant_term_comparison n hn).choose_spec.2`, and `RealizesStandardConv` is
`standardFromT0Std_realizesStandardConv` (the per-generator identity `T₀_sourceClass_eq_std` from the restriction formula).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

/-- **The class-level entry comparison for the actual `T₀`** (`PaperEntry` for `standardFromT0Std` of `line_constant_term_comparison`'s map). -/
theorem classLevel_paper_T0 (n : ℕ) (hn : 4 ≤ n) (D : CohomologicalCuspData n) (S : SphericalEntryData D.inducingData)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    PaperEntry n D.inducingData S I
      (standardFromT0Std D hn (planeEisensteinConvergent (by omega) D.inducingData)
        (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose
        (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose_spec.2) :=
  classLevel_paper n D.inducingData S I hw hv _
    (standardFromT0Std_realizesStandardConv D hn (planeEisensteinConvergent (by omega) D.inducingData)
      (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose
      (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose_spec.2)

/-- **The paper's constant-term map on the bad-plane section.** For `T₀ = (line_constant_term_comparison n hn).choose`, the good-line component
of `T₀` applied to the class of `badPlaneWeight · planeSource` is the printed scalar
`-2πi/(9(n+1))·L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` times the class of the paper's line section. -/
theorem T0_badPlane_goodComponent (n : ℕ) (hn : 4 ≤ n) (D : CohomologicalCuspData n) (S : SphericalEntryData D.inducingData)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    ∃ hSigP : IsSourceCocycle D.inducingData .line (fun y g => goodLineWeight g • cSigmaPaper n D.inducingData S.F y g),
      goodComponent n D.inducingData.chi .line
          ((TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose (SphericalEntryData.badPlaneClass S I).val) =
        S.printedScalar • (SourceQuotient.sourceToSummand D.inducingData .line
          ⟨fun y g => goodLineWeight g • cSigmaPaper n D.inducingData S.F y g, hSigP⟩).val := by
  obtain ⟨-, hSigP, hEq, -⟩ := classLevel_paper_T0 n hn D S I hw hv
  exact ⟨hSigP, by
    rw [← standardFromT0Std_apply_val D hn (planeEisensteinConvergent (by omega) D.inducingData)
      (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose
      (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose_spec.2]
    exact hEq⟩

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
