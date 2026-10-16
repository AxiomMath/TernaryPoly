module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelEichler
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Dictionary
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RESupply

@[expose] public section


/-!
# The paper-normalized class-level entry: the printed scalar against the paper-sign line section

The paper (`ar:eq:globalentry`) states the entry scalar of the good-line component of the
bad-plane section as `-2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1) = c_∞ · (1/9) ∏_{p≠3} c_p`, "expressed in the
induced-section and differential-form normalizations fixed above", where `c_∞` is computed *relative to the
line seed `σ_h`* built from the **same** `h` as the plane seed `ω_h`.

The library's line source `lineSource D E'` is built from the sign-twisted Eichler cocycle; its integral cochain
`cSigma` carries the line datum `(-1)^{n+1}(n+1) c_F^{line} F/2` (`lineHolData`), whereas the plane datum is
`(-1)^n (n+1) c_F F/2` (`planeHolData`).  So `lineSource D E'` is *minus* the line section of the paper's pair
(`σ` with the plane-sign datum `lineHolDataPaper`).  This file makes that statement precise and proves the resulting
class-level comparison with the **printed** scalar, with no rescaling:

* `lineIntG_neg`, `cSigmaPaper_eq_neg`: the line integral cochain `cSigmaPaper` of the line seed with the plane-sign
  datum `lineHolDataPaper` is `-cSigma`;
* `classLevel_paper`: for `S`, `I` as in `classLevel_badPlane_eichler` and any `T` realizing the standard operator,
  the good-line component of `T[badPlaneWeight · planeSource]` is `S.printedScalar` times the class of
  `goodLineWeight · cSigmaPaper` (the paper's line section), and that class is minus the class of
  `goodLineWeight · lineSource` (`entryScalar n S.rBad = -S.printedScalar` is `classLevel_badPlane_eichler`).

Formalized by Claude Sonnet 5.5.
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

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The line integral cochain of the line seed is odd in the datum `h`. -/
theorem lineIntG_neg (n : ℕ) (h : ℂ → ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    lineIntG n (fun z => -h z) M Γ₀ Γ₁ Γ₂ κ = -lineIntG n h M Γ₀ Γ₁ Γ₂ κ := by
  unfold lineIntG
  rw [← integral_neg]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun p _ => ?_
  simp only [twPullLine]
  rw [lineFormPair_lineSeedForm, lineFormPair_lineSeedForm, rho_C_mul, rho_C_mul, coeff_C_mul,
    coeff_C_mul]
  ring

/-- The coefficient `κ` of the line integral cochain of the paper's line section: the line seed `σ_h` with the
*plane-sign* datum `lineHolDataPaper` (the same sign as the plane datum of the pair `(ω_h, σ_h)`). -/
def cSigmaPaperCoeff (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) : ℂ :=
  lineIntG n (lineHolDataPaper n D F g 1) (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ +
  lineIntG n (lineHolDataPaper n D F g (atInfinity UpperHalfPlane.J)) (lamM * (realGroup g).val)
    (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ

/-- The line integral cochain of the paper's line section, as a homogeneous polynomial. -/
def cSigmaPaper (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  ofCoeffs n (cSigmaPaperCoeff n D F y g)

theorem cSigmaPaperCoeff_eq_neg (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) : cSigmaPaperCoeff n D F y g κ = -cSigmaCoeff n D F y g κ := by
  have e : ∀ x, lineHolData n D F g x = fun z => -lineHolDataPaper n D F g x z := fun x =>
    funext fun z => lineHolData_eq_neg n D F g x z
  unfold cSigmaPaperCoeff cSigmaCoeff
  rw [e, e, lineIntG_neg, lineIntG_neg]
  ring

/-- **The paper's line section is minus the library line integral cochain.** -/
theorem cSigmaPaper_eq_neg (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : cSigmaPaper n D F y g = -cSigma n D F y g := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro κ
  have h1 : ((cSigmaPaper n D F y g : HomogeneousPoly n) : Poly).coeff κ =
      if κ.degree = n then cSigmaPaperCoeff n D F y g κ else 0 := coeff_ofCoeffs n _ κ
  rw [h1, Submodule.coe_neg, MvPolynomial.coeff_neg, coeff_cSigma]
  split_ifs
  · exact cSigmaPaperCoeff_eq_neg n D F y g κ
  · simp

theorem isSourceCocycle_smul_neg {n : ℕ} (D : InducingData n) {c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    (hc : IsSourceCocycle D .line c) : IsSourceCocycle D .line (fun y g => -c y g) := by
  have := SourceSpace.source_smul D .line (-1 : ℂ) c hc
  have e : (fun y g => (-1 : ℂ) • c y g) = fun y g => -c y g :=
    funext fun y => funext fun g => neg_one_smul ℂ (c y g)
  rwa [e] at this


namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (I : EichlerInput D.cusp n)

include S

/-- The bad-plane section of the Eichler plane source is a source cocycle. -/
theorem badPlane_isSourceCocycle :
    IsSourceCocycle D .plane (fun y g => badPlaneWeight g • planeSource D (planeLevi I) y g) :=
  isSourceCocycle_smul_weight D badPlaneWeight_planeWeight _ (planeSource_isSourceCocycle D _ S.hχ)

/-- The good-line component of the Eichler line source is a source cocycle. -/
theorem goodLine_isSourceCocycle :
    IsSourceCocycle D .line (fun y g => goodLineWeight g • lineSource D (lineLevi I) y g) :=
  isSourceCocycle_smul_lineWeight D goodLineWeight_lineWeight _ (lineSource_isSourceCocycle D _ S.hχ)

end SphericalEntryData

/-- The conclusion of `classLevel_paper`. -/
def PaperEntry (n : ℕ) (D : InducingData n) (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) : Prop :=
    S.printedScalar ≠ 0 ∧
      ∃ hSigP : IsSourceCocycle D .line (fun y g => goodLineWeight g • cSigmaPaper n D S.F y g),
        goodComponent n D.chi .line
            (T (SourceQuotient.sourceToSummand D .plane
              ⟨fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g,
                SphericalEntryData.badPlane_isSourceCocycle S I⟩)).val =
          S.printedScalar • (SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hSigP⟩).val ∧
        (SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hSigP⟩).val =
          -(SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g,
              SphericalEntryData.goodLine_isSourceCocycle S I⟩).val

/-- If `J` agrees with `c • Σ` on the support of a weight `w` (with `c ≠ 0`) and `w • J` is a source
cocycle, then `w • Σ` is a source cocycle. -/
theorem isSourceCocycle_weight_smul_of_support {n : ℕ} (D : InducingData n) (w : AdelicGL → ℂ)
    (Sg : SourceCochain n) (c : ℂ) (hc : c ≠ 0) (J : SourceSpace.sourceCocycles D .line)
    (hJsupp : ∀ y g, w g ≠ 0 → J.val y g = c • Sg y g)
    (hJ : IsSourceCocycle D .line (fun y g => w g • J.val y g)) :
    IsSourceCocycle D .line (fun y g => w g • Sg y g) := by
  have hwline : (fun y g => w g • J.val y g) = fun y g => c • (w g • Sg y g) := by
    funext y g
    by_cases hg : w g = 0
    · simp [hg]
    · rw [hJsupp y g hg, smul_comm]
  have := SourceSpace.source_smul D .line c⁻¹ _ hJ
  refine (funext fun y => funext fun g => ?_ :
    (fun y g => c⁻¹ • (w g • J.val y g)) = fun y g => w g • Sg y g) ▸ this
  show c⁻¹ • (w g • J.val y g) = _
  rw [show w g • J.val y g = c • (w g • Sg y g) from congrFun (congrFun hwline y) g, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

/-- Elementary bookkeeping for signs: if `g = a • L`, `a = -p` and `P = -L`, then `g = p • P`. -/
theorem eq_smul_of_eq_smul_of_eq_neg {M : Type*} [AddCommGroup M] [Module ℂ M] {g L P : M} {a p : ℂ}
    (H : g = a • L) (hs : a = -p) (hP : P = -L) : g = p • P := by
  rw [H, hs, hP, neg_smul, smul_neg]

/-- **ML5: the printed scalar against the paper's line section.**  Let `S` be the finite spherical datum of the level-one
eigenform `h` (weight `k = n + 3`, `4 ≤ n`) and `I` the Eichler input of the same weight and vector.  For any `T` realizing
the standard operator:

* `S.printedScalar = -2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` (the paper's `ar:eq:globalentry`) is nonzero;
* the line cochain `goodLineWeight · cSigmaPaper` of the paper's line section (the line seed `σ_h` with the datum of the
  same sign as the plane seed `ω_h`) is a source cocycle;
* the good-line component of `T[badPlaneWeight · planeSource]` equals `S.printedScalar` times the class of that cocycle;
* the class of the paper's line section is **minus** the class of the library's line source
  `goodLineWeight · lineSource D (lineLevi I)` (the sign of the library's sign-twisted line cocycle, `lineHolData_eq_neg`).

Equivalently (`classLevel_badPlane_eichler`) the scalar against the library line source is `entryScalar n S.rBad =
-S.printedScalar`.  No rescaling is involved: the two statements differ by exactly the identification
`lineSource = -σ_h`. -/
theorem classLevel_paper (n : ℕ) (D : InducingData n) (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T) :
    PaperEntry n D S I T := by
  unfold PaperEntry
  have hn : 4 ≤ n := by have := S.large; omega
  have hE := SphericalEntryData.planeLevi_alpha (I := I) hw hv
  have hE' := SphericalEntryData.lineLevi_alpha (I := I) hw hv
  have holo := SphericalEntryData.holomorphic_F (I := I) hw hv
  have hc : ∀ g : RealGL3, componentCharacter D.chi g = 1 :=
    componentCharacter_eq_one_of_integral D.chi S.hχ
  have decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖S.F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M :=
    fun x => decay_of_weight D.cusp S.halfWeight S.weight S.vector x
  have hr : S.rBad ≠ 0 := by
    rw [S.rBad_eq_rPrint]
    exact S.rPrint_ne_zero
  have hRa : IsSourceCocycle D .plane (fun y g => cOmega n D S.F y g) :=
    cOmega_isSourceCocycle D S.F holo (SphericalEntryData.planeLevi I) hE hc S.hχ (continuousStages D)
      S.halfWeight S.vector (fixed_of_spherical D.cusp S.vector S.spherical) rfl
  have hobtain1 := classLevel_badPlane_eichler n D S I hw hv T hT
  obtain ⟨hne, hsign, H⟩ := hobtain1
  have hobtain2 := classLevel_of_Ra n hn D badPlaneWeight_planeWeight goodLineWeight_lineWeight
    (SphericalEntryData.planeLevi I) (SphericalEntryData.lineLevi I) S.F hE hE' hc S.hχ holo decay T hT
    (standardEndpointIntegral hn) S.rBad hr (badPlaneEntryIdentity S) hRa
  obtain ⟨_, H0⟩ := hobtain2
  have hobtain3 := H0 (SphericalEntryData.badPlane_isSourceCocycle S I)
    (SphericalEntryData.goodLine_isSourceCocycle S I)
  obtain ⟨J, _, hJsupp, hJ, _⟩ := hobtain3
  have hsc : entryScalar n S.rBad ≠ 0 := hne
  have hSig : IsSourceCocycle D .line (fun y g => goodLineWeight g • cSigma n D S.F y g) :=
    isSourceCocycle_weight_smul_of_support D goodLineWeight (cSigma n D S.F) (entryScalar n S.rBad) hsc J
      hJsupp hJ
  have hSigP : IsSourceCocycle D .line (fun y g => goodLineWeight g • cSigmaPaper n D S.F y g) := by
    have := isSourceCocycle_smul_neg D hSig
    refine (funext fun y => funext fun g => ?_ :
      (fun y g => -(goodLineWeight g • cSigma n D S.F y g)) =
        fun y g => goodLineWeight g • cSigmaPaper n D S.F y g) ▸ this
    rw [cSigmaPaper_eq_neg, smul_neg]
  have hclass : SourceQuotient.sourceToSummand D .line
        ⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hSigP⟩ =
      -SourceQuotient.sourceToSummand D .line
        ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g,
          SphericalEntryData.goodLine_isSourceCocycle S I⟩ := by
    have e2 := sourceToSummand_cSigma_eq_lineSource_weight D S.F holo (SphericalEntryData.lineLevi I) hE' hc S.hχ
      goodLineWeight_lineWeight hSig
    have e : (⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hSigP⟩ :
        SourceSpace.sourceCocycles D .line) =
        (-1 : ℂ) • (⟨fun y g => goodLineWeight g • cSigma n D S.F y g, hSig⟩ :
          SourceSpace.sourceCocycles D .line) := by
      apply Subtype.ext
      funext y g
      show goodLineWeight g • cSigmaPaper n D S.F y g = (-1 : ℂ) • (goodLineWeight g • cSigma n D S.F y g)
      rw [cSigmaPaper_eq_neg, smul_neg]
      exact (neg_one_smul ℂ (goodLineWeight g • cSigma n D S.F y g)).symm
    exact (congrArg (SourceQuotient.sourceToSummand D .line) e).trans
      ((map_smul (SourceQuotient.sourceToSummand D .line) (-1 : ℂ) _).trans
        ((neg_one_smul ℂ _).trans (congrArg Neg.neg e2)))
  have hval : (SourceQuotient.sourceToSummand D .line
        ⟨fun y g => goodLineWeight g • cSigmaPaper n D S.F y g, hSigP⟩).val =
      -(SourceQuotient.sourceToSummand D .line
        ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g,
          SphericalEntryData.goodLine_isSourceCocycle S I⟩).val :=
    (congrArg Subtype.val hclass).trans (Submodule.coe_neg _ _)
  exact ⟨S.printedScalar_ne_zero, hSigP,
    eq_smul_of_eq_smul_of_eq_neg
      (H (SphericalEntryData.badPlane_isSourceCocycle S I) (SphericalEntryData.goodLine_isSourceCocycle S I))
      hsign hval, hval⟩


/-- **ML5 for the actual datum.**  For an inducing datum `D` of odd degree with trivial character and a spherical
cuspidal constituent (the hypotheses of the per-datum detection), the entry package `P` of N2
(`exists_sphericalEntryPackage`: the finite spherical datum `P.S` and the Eichler input `P.I` of the same vector) exists,
and for it any `T` realizing the standard operator satisfies `classLevel_paper`. -/
theorem classLevel_paper_of_spherical (n : ℕ) (D : InducingData n) (hodd : Odd n)
    (hχ : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T) :
    ∃ P : SphericalEntryPackage D, PaperEntry n D P.S P.I T := by
  have hobtain4 := exists_sphericalEntryPackage D hodd hχ hsph
  obtain ⟨P⟩ := hobtain4
  exact ⟨P, classLevel_paper n D P.S P.I P.halfWeight_eq P.vector_eq T hT⟩

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
