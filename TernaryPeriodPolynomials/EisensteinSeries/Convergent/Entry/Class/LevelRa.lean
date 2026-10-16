module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.ClassLevel
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Edge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Edge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Weight
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Weight

@[expose] public section


/-!
# The class-level entry comparison with the class identifications (R-b) discharged

`classLevel_of_Ra`: `classLevel_conditional` with the two class identifications R-b proved
(`sourceToSummand_cOmega_eq_planeSource`, `sourceToSummand_cSigma_eq_lineSource`).  **Still CONDITIONAL** on R-a
(`hRa`: the plane integral cochain `cOmega` is a source cocycle), R-c (`StandardEndpointIntegral` for
`4 ≤ n`) and R-e (`FiniteEntryIdentity D ι ιL F r`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **CONDITIONAL class-level entry comparison, R-b discharged (still not the completion).** `ι` is the finite weight
of the plane section (`PlaneWeight ι`; `ι = 1` spherical, the `P K₁(3)` indicator for the bad plane) and `ιL` the finite
weight of the line component compared (`LineWeight ιL`; `ιL = 1` the whole spherical line section, the indicator of the
good-line orbit for the good-line component of the bad-plane section).  Hypotheses: `hRa` (R-a, for the spherical
integral cochain), `hRc` (R-c), `hRe` (R-e, only on the support of `ιL`). -/
theorem classLevel_of_Ra (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) {ι ιL : AdelicGL → ℂ} (hι : PlaneWeight ι)
    (hιL : LineWeight ιL)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hE : ∀ A, E.α A = eichlerNormal n F A) (hE' : ∀ A, E'.α A = eichlerNormalTw n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (holomorphic : ∀ x, DifferentiableOn ℂ (F x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hRc : StandardEndpointIntegral n) (r : ℂ) (hr : r ≠ 0) (hRe : FiniteEntryIdentity D ι ιL F r)
    (hRa : IsSourceCocycle D .plane (fun y g => cOmega n D F y g)) :
    entryScalar n r ≠ 0 ∧ ∀ (hps : IsSourceCocycle D .plane (fun y g => ι g • planeSource D E y g))
      (hls : IsSourceCocycle D .line (fun y g => ιL g • lineSource D E' y g)),
      ∃ J : SourceSpace.sourceCocycles D .line,
        T (SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • planeSource D E y g, hps⟩) =
          SourceQuotient.sourceToSummand D .line J ∧
        (∀ y g, ιL g ≠ 0 → J.val y g = entryScalar n r • cSigma n D F y g) ∧
        ∃ hJ : IsSourceCocycle D .line (fun y g => ιL g • J.val y g),
          SourceQuotient.sourceToSummand D .line ⟨fun y g => ιL g • J.val y g, hJ⟩ =
            entryScalar n r • SourceQuotient.sourceToSummand D .line
              ⟨fun y g => ιL g • lineSource D E' y g, hls⟩ :=
  classLevel_conditional n hn D ι ιL hι.finite hιL E E' F holomorphic decay T hT hRc r hr hRe
    (isSourceCocycle_smul_weight D hι _ hRa)
    (fun _ => sourceToSummand_cOmega_eq_planeSource_weight D F holomorphic E hE hc hχ hι
      (isSourceCocycle_smul_weight D hι _ hRa))
    (fun hSig _ => sourceToSummand_cSigma_eq_lineSource_weight D F holomorphic E' hE' hc hχ hιL hSig)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
