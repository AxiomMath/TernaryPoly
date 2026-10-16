module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.ClassLevelPaper
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryHeckeDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LinePeriod

@[expose] public section


/-!
# Shapiro coordinates of component projections and of the Eichler sections (paper-route detection)

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **The Shapiro coordinate of a component projection** is the coordinate times the weight at the cusp flag. -/
theorem cuspRes_flagProj {n : ℕ} {χ : RankOneCharacter} {s : Side} (good : Bool) (w : Flags s → ℂ)
    (hw : ∀ (γ : rationalLevel) (x : Flags s), w (γ.val • x) = w x) (a : StratumH2 n χ s) :
    cuspRes n χ s good (flagProj w hw a) = w (cuspFlag s good) • cuspRes n χ s good a := by
  induction a using Submodule.Quotient.induction_on with
  | H z =>
    have e1 : cuspRes n χ s good (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) s) (flagCocMap w hw z)) =
        classOf (cuspLevel s good) (rationalCoefficientComponent n χ)
          (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) (cuspFlag s good)
            (flagCocMap w hw z)) :=
      fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n χ) (cuspFlag s good) _
    have e2 : cuspRes n χ s good (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) s) z) =
        classOf (cuspLevel s good) (rationalCoefficientComponent n χ)
          (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) (cuspFlag s good) z) :=
      fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n χ) (cuspFlag s good) _
    have e3 : fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) (cuspFlag s good)
        (flagCocMap w hw z) =
        w (cuspFlag s good) • fixedPointCycle rationalLevel (rationalCoefficientComponent n χ)
          (cuspFlag s good) z := rfl
    change cuspRes n χ s good (flagProj w hw (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) s) z)) = w (cuspFlag s good) •
        cuspRes n χ s good (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n χ) s) z)
    rw [flagProj_classOf, e1, e2, e3]
    exact map_smul _ _ _


theorem goodWeight_cuspFlag_true (s : Side) : goodWeight s (cuspFlag s true) = 1 := by
  unfold goodWeight
  rw [ite_eq_left ((cuspFlag_good_iff s true).mpr rfl)]

/-- The good-flag component does not change the coordinate at the good cusp of its side. -/
theorem cuspRes_goodComponent {n : ℕ} {χ : RankOneCharacter} (s : Side) (a : StratumH2 n χ s) :
    cuspRes n χ s true (goodComponent n χ s a) = cuspRes n χ s true a := by
  unfold goodComponent
  rw [cuspRes_flagProj, goodWeight_cuspFlag_true, one_smul]

/-- **The bad-plane section has zero coordinate at the good-plane cusp.** -/
theorem cuspRes_plane_true_badPlane {n : ℕ} (D : InducingData n)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n) (hc : IsSourceCocycle D .plane c)
    (hc' : IsSourceCocycle D .plane (fun y g => badPlaneWeight g • c y g)) :
    cuspRes n D.chi .plane true
      (SourceSpace.sourceClass D .plane ⟨fun y g => badPlaneWeight g • c y g, hc'⟩) = 0 := by
  have hw : ∀ (γ : rationalLevel) (x : Flags .plane),
      (fun x => 1 - goodWeight .plane x) (γ.val • x) = (fun x => 1 - goodWeight .plane x) x := by
    intro γ x
    simp only [goodWeight_invariant]
  rw [← flagProj_sourceClass D .plane (fun x => 1 - goodWeight .plane x) hw badPlaneWeight
    (fun q => badPlaneWeight_rational q) c hc hc', cuspRes_flagProj, goodWeight_cuspFlag_true]
  simp

/-- **The good-line section has the coordinate of the unweighted source at the good-line cusp.** -/
theorem cuspRes_line_true_goodLine {n : ℕ} (D : InducingData n)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n) (hc : IsSourceCocycle D .line c)
    (hc' : IsSourceCocycle D .line (fun y g => goodLineWeight g • c y g)) :
    cuspRes n D.chi .line true
      (SourceSpace.sourceClass D .line ⟨fun y g => goodLineWeight g • c y g, hc'⟩) =
    cuspRes n D.chi .line true (SourceSpace.sourceClass D .line ⟨c, hc⟩) := by
  rw [← flagProj_sourceClass D .line (goodWeight .line) (goodWeight_invariant .line) goodLineWeight
    (fun q => goodLineWeight_rational q) c hc hc', cuspRes_flagProj, goodWeight_cuspFlag_true, one_smul]


open TernaryPeriodPolynomials.SourceConstruction TernaryPeriodPolynomials.AnalyticClasses in
/-- **The good-line coordinate of the line source of an Eichler input is nonzero** (odd degree, trivial character):
the arithmetic period class of the sign-twisted Eichler cocycle of any Eichler input is nonzero
(`signEichlerCocycle_period_class_ne_zero`), and `lineSource_cuspRes_goodLine_ne_zero` transports it by the pivot swap. -/
theorem lineSource_cuspRes_ne_zero_of_eichler {n : ℕ} (D : InducingData n) (hchi : D.chi = trivialCharacter)
    (I : EichlerInput D.cusp n) (odd : Odd n)
    (hls : IsSourceCocycle D .line (lineSource D (SphericalEntryData.lineLevi I))) :
    cuspRes n D.chi .line true (SourceSpace.sourceClass D .line ⟨lineSource D (SphericalEntryData.lineLevi I), hls⟩)
      ≠ 0 := by
  obtain ⟨ψ, hψ, hψ0⟩ := I.signEichlerCocycle_period_class_ne_zero (continuousStages D) odd
  refine lineSource_cuspRes_goodLine_ne_zero D (SphericalEntryData.lineLevi I) hchi odd.pos
    (dlCocycleOf n ψ) ?_ (dlCocycleOf_ne_zero ψ hψ0)
    (SourceSpace.evaluatedSource_realizes D .line ⟨lineSource D (SphericalEntryData.lineLevi I), hls⟩)
  intro m
  exact congrArg (binarySwap n) ((hψ (dlIntPivot m)).trans
    (congrArg (fun A => (SphericalEntryData.lineLevi I).α A 1) (dlIntPivot_map m)))

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
