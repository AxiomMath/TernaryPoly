module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelRa
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.FlagProjection
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Ra
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay

@[expose] public section


/-!
# The class-level entry comparison, stated on the component projection

`classLevel_proj`: the comparison `T [ι·planeSource] = c · [lineSource]` holds after applying the component projection
`flagProj w` of the line stratum cohomology (`Entry/FlagProjection`) for any arithmetically invariant flag weight `w`
represented by the adelic line weight `ιL` (`ιL(ρ(q⁻¹)) = w(qP)`): `flagProj w (T [ι·planeSource]) = c · [ιL·lineSource]`.
For `w` the indicator of the good flags (`goodWeight`) this is the statement for the **good-line component**
(`classLevel_good`): `goodComponent (T [ι·planeSource]) = c · [ιL·lineSource]`, `c = (-r)(-2πi/(n+1)) ≠ 0`.  It is
stated on classes (no choice of representative); the hypotheses are those of `classLevel_of_Ra` (still CONDITIONAL on
R-a, R-c, R-e).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **Class-level entry comparison on a component projection (CONDITIONAL on R-a, R-c, R-e).** -/
theorem classLevel_proj (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) {ι ιL : AdelicGL → ℂ} (hι : PlaneWeight ι)
    (hιL : LineWeight ιL)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hE : ∀ A, E.α A = eichlerNormal n F A) (hE' : ∀ A, E'.α A = eichlerNormalTw n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (holomorphic : ∀ x, DifferentiableOn ℂ (F x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hRc : StandardEndpointIntegral n) (r : ℂ) (hr : r ≠ 0) (hRe : FiniteEntryIdentity D ι ιL F r)
    (hRa : IsSourceCocycle D .plane (fun y g => cOmega n D F y g))
    (w : Flags .line → ℂ) (hw : ∀ (γ : rationalLevel) (x : Flags .line), w (γ.val • x) = w x)
    (hιw : ∀ q : RationalGL3, ιL (rationalGroup q⁻¹) = w (QuotientGroup.mk q)) :
    entryScalar n r ≠ 0 ∧ ∀ (hps : IsSourceCocycle D .plane (fun y g => ι g • planeSource D E y g))
      (hls : IsSourceCocycle D .line (fun y g => ιL g • lineSource D E' y g)),
      flagProj (χ := D.chi) w hw
          (T (SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • planeSource D E y g, hps⟩)).val =
        entryScalar n r • (SourceQuotient.sourceToSummand D .line
          ⟨fun y g => ιL g • lineSource D E' y g, hls⟩).val := by
  have hobtain1 := classLevel_of_Ra n hn D hι hιL E E' F hE hE' hc hχ holomorphic decay T hT hRc r hr hRe hRa
  obtain ⟨hc0, H⟩ := hobtain1
  refine ⟨hc0, fun hps hls => ?_⟩
  have hobtain2 := H hps hls
  obtain ⟨J, hTJ, _, hJ, hJclass⟩ := hobtain2
  rw [hTJ]
  have h1 : (SourceQuotient.sourceToSummand D .line J).val = SourceSpace.sourceClass D .line J := rfl
  rw [h1, flagProj_sourceClass D .line w hw ιL hιw J.val J.property hJ]
  have h2 := congrArg (fun a : boundarySummand D .line => a.val) hJclass
  exact h2

/-- **The good-line component** (CONDITIONAL on R-a, R-c, R-e): `ιL` represents the indicator of the good lines. -/
theorem classLevel_good (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) {ι ιL : AdelicGL → ℂ} (hι : PlaneWeight ι)
    (hιL : LineWeight ιL)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hE : ∀ A, E.α A = eichlerNormal n F A) (hE' : ∀ A, E'.α A = eichlerNormalTw n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (holomorphic : ∀ x, DifferentiableOn ℂ (F x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hRc : StandardEndpointIntegral n) (r : ℂ) (hr : r ≠ 0) (hRe : FiniteEntryIdentity D ι ιL F r)
    (hRa : IsSourceCocycle D .plane (fun y g => cOmega n D F y g))
    (hιw : ∀ q : RationalGL3, ιL (rationalGroup q⁻¹) = goodWeight .line (QuotientGroup.mk q)) :
    entryScalar n r ≠ 0 ∧ ∀ (hps : IsSourceCocycle D .plane (fun y g => ι g • planeSource D E y g))
      (hls : IsSourceCocycle D .line (fun y g => ιL g • lineSource D E' y g)),
      goodComponent n D.chi .line
          (T (SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • planeSource D E y g, hps⟩)).val =
        entryScalar n r • (SourceQuotient.sourceToSummand D .line
          ⟨fun y g => ιL g • lineSource D E' y g, hls⟩).val :=
  classLevel_proj n hn D hι hιL E E' F hE hE' hc hχ holomorphic decay T hT hRc r hr hRe hRa
    (goodWeight .line) (goodWeight_invariant .line) hιw


/-- **The good-line component of the class-level entry comparison, R-a discharged** (CONDITIONAL only on R-c, R-e).
`F` is the weighted scalar realization of the smooth finite-level Eichler vector `v` (as in the Eichler construction),
`R-a` (`cOmega_isSourceCocycle`) is proved, and the only hypotheses are `hRc` (R-c, proved for `4 ≤ n`) and `hRe`
(R-e, the guarded finite identity). -/
theorem classLevel_good_of_eichler (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) {ι ιL : AdelicGL → ℂ}
    (hι : PlaneWeight ι) (hιL : LineWeight ιL)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n) (hw : ℤ) (v : D.cusp.smooth)
    (fixed : v.val ∈ BinaryLevel.fixedSubspace D.cusp BinaryLevel.finiteCongruence)
    (hE : ∀ A, E.α A = eichlerNormal n (cuspScalarWeightedRealization D.cusp hw v) A)
    (hE' : ∀ A, E'.α A = eichlerNormalTw n (cuspScalarWeightedRealization D.cusp hw v) A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (holomorphic : ∀ x, DifferentiableOn ℂ (cuspScalarWeightedRealization D.cusp hw v x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im →
      ‖cuspScalarWeightedRealization D.cusp hw v x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hRc : StandardEndpointIntegral n) (r : ℂ) (hr : r ≠ 0)
    (hRe : FiniteEntryIdentity D ι ιL (cuspScalarWeightedRealization D.cusp hw v) r)
    (hιw : ∀ q : RationalGL3, ιL (rationalGroup q⁻¹) = goodWeight .line (QuotientGroup.mk q)) :
    entryScalar n r ≠ 0 ∧ ∀ (hps : IsSourceCocycle D .plane (fun y g => ι g • planeSource D E y g))
      (hls : IsSourceCocycle D .line (fun y g => ιL g • lineSource D E' y g)),
      goodComponent n D.chi .line
          (T (SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • planeSource D E y g, hps⟩)).val =
        entryScalar n r • (SourceQuotient.sourceToSummand D .line
          ⟨fun y g => ιL g • lineSource D E' y g, hls⟩).val :=
  classLevel_good n hn D hι hιL E E' (cuspScalarWeightedRealization D.cusp hw v) hE hE' hc hχ holomorphic decay T hT
    hRc r hr hRe
    (cOmega_isSourceCocycle D _ holomorphic E hE hc hχ (continuousStages D) hw v fixed rfl) hιw

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
