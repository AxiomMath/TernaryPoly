module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.ClassLevelPaper
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Normalization

@[expose] public section


/-!
# The normalization dictionary of the Appendix C entries (plane/line scalars `λ_pl`, `λ_li`)

Formalized by Claude Sonnet 5.5.

The paper computes the real entry `c_∞ = -2πi/(n+1)` relative to the line seed `σ_h` built from the SAME function `h` as the plane
seed `ω_h` ("Changing orientation or period normalization rescales this nonzero entry"), the finite entry
`(T₃φ)(g₀) = v₀/9` and the Euler factors `c_p`, and states the product `eq:globalentry`
`-2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` "in the induced-section and differential-form normalizations fixed above".

The library's two sources are `planeSource` and `lineSource`, the integral cochains of the two seeds with the data
`h_plane = (-1)ⁿ (n+1) c_F F/2` and `h_line = (-1)^{n+1} (n+1) c_F^{line} F/2` (`planeHolData`, `lineHolData`).  The dictionary between the
paper's classes and the library's classes is:

* the paper's bad-plane section (the plane seed `ω_h` with the plane datum, supported on the bad-plane orbit `P K₁(3)`) is the class of
  `badPlaneWeight · cΩ`, which equals the class of `badPlaneWeight · planeSource` (`λ_pl = 1`);
* the paper's good-line section (the line seed `σ_h` with the SAME sign as the plane datum, `lineHolDataPaper`) is the class of
  `goodLineWeight · cΣ^{paper}`, and `cΣ^{paper} = -cΣ`, so it equals `-` the class of `goodLineWeight · lineSource` (`λ_li = -1`);
* hence `(λ_pl / λ_li) · entryScalar n r_print = printedScalar = -2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`.

The only sign is the factor `(-1)^{n+1}` versus `(-1)ⁿ` of the line versus plane datum (the library's line cocycle is the antisymmetrized
`P - J P'` Eichler normal form for the line coefficient system without determinant twist); it is a normalization of the line source and not
a rescaling of the entry up to a factor other than `-1`.  This is a convention statement, not a correction of the paper.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EntryDictionary

/-- The scalar relating the paper's bad-plane section to the library's `ι_{PK₁} · planeSource`. -/
def lamPl : ℂ := 1

/-- The scalar relating the paper's good-line section to the library's `goodLineWeight · lineSource`. -/
def lamLi : ℂ := -1

theorem lamPl_ne_zero : lamPl ≠ 0 := one_ne_zero

theorem lamLi_ne_zero : lamLi ≠ 0 := neg_ne_zero.2 one_ne_zero

/-- The data signs: `h_line = - h_line^{paper}`, i.e. `(-1)^{n+1}` versus `(-1)ⁿ`. -/
theorem datum_sign (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL) (x : BinaryAdelicGL)
    (z : ℂ) :
    lineHolData n D F g x z = lamLi * lineHolDataPaper n D F g x z := by
  rw [lineHolData_eq_neg, lamLi, neg_one_mul]

/-- **Convention covariance.**  If the paper's sections are the library's sections rescaled by `μ_pl, μ_li ≠ 0`, the scalar of the
entry transforms by `μ_pl / μ_li`; in particular a free rescaling changes the printed scalar but not its nonvanishing. -/
theorem scalar_covariance {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (T : M →ₗ[ℂ] N) (x : M) (y : N) (s μ μ' : ℂ) (hμ' : μ' ≠ 0) (h : T x = s • y) :
    T (μ • x) = ((μ / μ') * s) • (μ' • y) := by
  rw [map_smul, h, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **The entry dictionary.**  For the finite spherical datum `S` of the level-one eigenform `h` and the Eichler input `I` of the
same weight and vector, and any `T` realizing the standard operator:

1. `paperPlane = λ_pl · libraryPlane`, `paperLine = λ_li · libraryLine` as classes (`λ_pl = 1`, `λ_li = -1`);
2. the good-line component of `T[libraryPlane]` is `entryScalar n r_print · libraryLine` and that of `T[paperPlane]` is
   `printedScalar · paperLine`;
3. `(λ_pl / λ_li) · entryScalar n r_print = printedScalar`, and `printedScalar` is the paper's `eq:globalentry`. -/
theorem entry_dictionary (n : ℕ) (D : InducingData n) (S : SphericalEntryData D) (I : EichlerInput D.cusp n)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T) :
    ∃ (hPP : IsSourceCocycle D .plane (fun y g => badPlaneWeight g • cOmega n D S.F y g))
      (hPL : IsSourceCocycle D .plane
        (fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g))
      (hLP : IsSourceCocycle D .line (fun y g => goodLineWeight g • cSigmaPaper n D S.F y g))
      (hLL : IsSourceCocycle D .line
        (fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g)),
      (SourceQuotient.sourceToSummand D .plane ⟨fun y g => badPlaneWeight g • cOmega n D S.F y g, hPP⟩).val =
          lamPl • (SourceQuotient.sourceToSummand D .plane
            ⟨fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g, hPL⟩).val ∧
      (SourceQuotient.sourceToSummand D .line ⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hLP⟩).val =
          lamLi • (SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g, hLL⟩).val ∧
      goodComponent n D.chi .line
          (T (SourceQuotient.sourceToSummand D .plane
            ⟨fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g, hPL⟩)).val =
        entryScalar n S.rBad • (SourceQuotient.sourceToSummand D .line
          ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g, hLL⟩).val ∧
      goodComponent n D.chi .line
          (T (SourceQuotient.sourceToSummand D .plane
            ⟨fun y g => badPlaneWeight g • cOmega n D S.F y g, hPP⟩)).val =
        S.printedScalar • (SourceQuotient.sourceToSummand D .line
          ⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hLP⟩).val ∧
      S.rBad = S.rPrint ∧ (lamPl / lamLi) * entryScalar n S.rBad = S.printedScalar ∧
      S.printedScalar = -2 * Real.pi * Complex.I / (9 * ((n : ℂ) + 1)) * globalEntryRatio S.form := by
  have hE := SphericalEntryData.planeLevi_alpha (I := I) hw hv
  have holo := SphericalEntryData.holomorphic_F (I := I) hw hv
  have hc : ∀ g : RealGL3, componentCharacter D.chi g = 1 :=
    componentCharacter_eq_one_of_integral D.chi S.hχ
  have hRa : IsSourceCocycle D .plane (fun y g => cOmega n D S.F y g) :=
    cOmega_isSourceCocycle D S.F holo (SphericalEntryData.planeLevi I) hE hc S.hχ (continuousStages D)
      S.halfWeight S.vector (fixed_of_spherical D.cusp S.vector S.spherical) rfl
  have hPP : IsSourceCocycle D .plane (fun y g => badPlaneWeight g • cOmega n D S.F y g) :=
    isSourceCocycle_smul_weight D badPlaneWeight_planeWeight _ hRa
  have hPL := SphericalEntryData.badPlane_isSourceCocycle S I
  have hobtain1 := classLevel_paper n D S I hw hv T hT
  obtain ⟨_, hLP, hT1, hT2⟩ := hobtain1
  have hobtain2 := classLevel_badPlane_eichler n D S I hw hv T hT
  obtain ⟨_, hsign, H⟩ := hobtain2
  have hLL := SphericalEntryData.goodLine_isSourceCocycle S I
  refine ⟨hPP, hPL, hLP, hLL, ?_, ?_, ?_, ?_, S.rBad_eq_rPrint, ?_, ?_⟩
  · rw [lamPl, one_smul]
    rw [sourceToSummand_cOmega_eq_planeSource_weight D S.F holo (SphericalEntryData.planeLevi I) hE hc S.hχ
      badPlaneWeight_planeWeight hPP]
  · exact hT2.trans (neg_one_smul ℂ _).symm
  · exact H hPL hLL
  · have e := sourceToSummand_cOmega_eq_planeSource_weight D S.F holo (SphericalEntryData.planeLevi I) hE hc S.hχ
      badPlaneWeight_planeWeight hPP
    exact (congrArg (fun x => goodComponent n D.chi .line (T x).val) e).trans hT1
  · rw [hsign, lamPl, lamLi]
    ring
  · rfl

end TernaryPeriodPolynomials.Argument.EntryDictionary
