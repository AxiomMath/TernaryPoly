module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.ClassLevelPaper

@[expose] public section


/-!
# The class-level entry comparison with the finite entry identity as an input

`ClassLevelBadPlane.classLevel_badPlane`, `ClassLevelEichler.classLevel_badPlane_eichler` and
`ClassLevelPaper.classLevel_paper` obtain the finite entry identity `FiniteEntryIdentity D badPlaneWeight
goodLineWeight S.F S.rBad` from `badPlaneEntryIdentity S`, whose proof goes through the representation-theoretic
`entryPlaneIntegral_bad_general`.  The three theorems below are the same proofs with that identity as an explicit
hypothesis `hE` (or `hEntry`), so that the finite entry computed from the literal lattice/Hecke integral
(argument-flow target R2, `paper_finite_entry`) is consumed instead.  The closure of the `_of_entry` versions does not
contain `badPlaneEntryIdentity`.

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
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

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- **The good-line component of the bad-plane comparison, for a supplied finite entry identity.**  Verbatim
`classLevel_badPlane` with `badPlaneEntryIdentity S` replaced by the hypothesis `hEntry`. -/
theorem classLevel_badPlane_of_entry (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) (S : SphericalEntryData D)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n)
    (hE : ∀ A, E.α A = eichlerNormal n S.F A) (hE' : ∀ A, E'.α A = eichlerNormalTw n S.F A)
    (holomorphic : ∀ x, DifferentiableOn ℂ (S.F x) {z : ℂ | 0 < z.im})
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hEntry : FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad) :
    entryScalar n S.rBad ≠ 0 ∧ entryScalar n S.rBad = -S.printedScalar ∧
      ∀ (hps : IsSourceCocycle D .plane (fun y g => badPlaneWeight g • planeSource D E y g))
        (hls : IsSourceCocycle D .line (fun y g => goodLineWeight g • lineSource D E' y g)),
        goodComponent n D.chi .line
            (T (SourceQuotient.sourceToSummand D .plane
              ⟨fun y g => badPlaneWeight g • planeSource D E y g, hps⟩)).val =
          entryScalar n S.rBad • (SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • lineSource D E' y g, hls⟩).val := by
  have hc : ∀ g : RealGL3, componentCharacter D.chi g = 1 := componentCharacter_eq_one_of_integral D.chi S.hχ
  have decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im →
      ‖cuspScalarWeightedRealization D.cusp S.halfWeight S.vector x z‖ ^ 2 * z.im ^ (n + 3) ≤ M :=
    fun x => decay_of_weight D.cusp S.halfWeight S.weight S.vector x
  have hr : S.rBad ≠ 0 := by
    rw [S.rBad_eq_rPrint]
    exact S.rPrint_ne_zero
  have hobtain1 := classLevel_good_of_eichler n hn D badPlaneWeight_planeWeight goodLineWeight_lineWeight E E'
    S.halfWeight S.vector (fixed_of_spherical D.cusp S.vector S.spherical) hE hE' hc S.hχ holomorphic decay T hT
    (standardEndpointIntegral hn) S.rBad hr hEntry goodLineWeight_rational
  obtain ⟨h0, H⟩ := hobtain1
  refine ⟨h0, ?_, H⟩
  rw [S.rBad_eq_rPrint]
  exact S.entryScalar_rPrint

/-- **The good-line component of the bad-plane comparison for the actual Eichler Levi data, for a supplied finite
entry identity `hE`.**  Verbatim `classLevel_badPlane_eichler` with `badPlaneEntryIdentity S` replaced by `hE`. -/
theorem classLevel_badPlane_eichler_of_entry (n : ℕ) (D : InducingData n) (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hE : FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad) :
    entryScalar n S.rBad ≠ 0 ∧ entryScalar n S.rBad = -S.printedScalar ∧
      ∀ (hps : IsSourceCocycle D .plane
          (fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g))
        (hls : IsSourceCocycle D .line
          (fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g)),
        goodComponent n D.chi .line
            (T (SourceQuotient.sourceToSummand D .plane
              ⟨fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g, hps⟩)).val =
          entryScalar n S.rBad • (SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g, hls⟩).val :=
  classLevel_badPlane_of_entry n (by have := S.large; omega) D S (SphericalEntryData.planeLevi I)
    (SphericalEntryData.lineLevi I) (SphericalEntryData.planeLevi_alpha hw hv)
    (SphericalEntryData.lineLevi_alpha hw hv) (SphericalEntryData.holomorphic_F hw hv) T hT hE

/-- **ML5 with a supplied finite entry identity: the printed scalar against the paper's line section.**  Verbatim
`classLevel_paper` with `badPlaneEntryIdentity S` replaced by the hypothesis `hE`; the conclusion is `PaperEntry`. -/
theorem classLevel_paper_of_entry (n : ℕ) (D : InducingData n) (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hE : FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad) :
    PaperEntry n D S I T := by
  unfold PaperEntry
  have hn : 4 ≤ n := by have := S.large; omega
  have hEa := SphericalEntryData.planeLevi_alpha (I := I) hw hv
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
    cOmega_isSourceCocycle D S.F holo (SphericalEntryData.planeLevi I) hEa hc S.hχ (continuousStages D)
      S.halfWeight S.vector (fixed_of_spherical D.cusp S.vector S.spherical) rfl
  have hobtain2 := classLevel_badPlane_eichler_of_entry n D S I hw hv T hT hE
  obtain ⟨hne, hsign, H⟩ := hobtain2
  have hobtain3 := classLevel_of_Ra n hn D badPlaneWeight_planeWeight goodLineWeight_lineWeight
    (SphericalEntryData.planeLevi I) (SphericalEntryData.lineLevi I) S.F hEa hE' hc S.hχ holo decay T hT
    (standardEndpointIntegral hn) S.rBad hr hE hRa
  obtain ⟨_, H0⟩ := hobtain3
  have hobtain4 := H0 (SphericalEntryData.badPlane_isSourceCocycle S I)
    (SphericalEntryData.goodLine_isSourceCocycle S I)
  obtain ⟨J, _, hJsupp, hJ, _⟩ := hobtain4
  have hsc : entryScalar n S.rBad ≠ 0 := hne
  have hwline : (fun y g => goodLineWeight g • J.val y g) =
      fun y g => entryScalar n S.rBad • (goodLineWeight g • cSigma n D S.F y g) := by
    funext y g
    by_cases hg : goodLineWeight g = 0
    · simp [hg]
    · rw [hJsupp y g hg, smul_comm]
  have hSig : IsSourceCocycle D .line (fun y g => goodLineWeight g • cSigma n D S.F y g) := by
    have := SourceSpace.source_smul D .line (entryScalar n S.rBad)⁻¹ _ hJ
    refine (funext fun y => funext fun g => ?_ :
      (fun y g => (entryScalar n S.rBad)⁻¹ • (goodLineWeight g • J.val y g)) =
        fun y g => goodLineWeight g • cSigma n D S.F y g) ▸ this
    show (entryScalar n S.rBad)⁻¹ • (goodLineWeight g • J.val y g) = _
    rw [show goodLineWeight g • J.val y g = entryScalar n S.rBad • (goodLineWeight g • cSigma n D S.F y g) from
      congrFun (congrFun hwline y) g, smul_smul, inv_mul_cancel₀ hsc, one_smul]
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


end TernaryPeriodPolynomials.Argument.BoundaryComparison
