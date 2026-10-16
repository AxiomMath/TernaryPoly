module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitStep
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FiniteSetFibre
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitIntegrable

@[expose] public section


/-!
# Global limit: the Fubini step for adjoining one place

For `q ∉ T` (places `≠ 3`) and `F` integrable on `FiniteAwayThree²`:
`∫_{U_{T∪{q}}} F = ∫_{y ∈ (WS T)²} ∫_{x ∈ K_q²} F(atPlace q x + ι_T y)`, i.e. the integral over `U_{T ∪ {q}}` is the iterated integral over the `T`-coordinates `y`
and the new coordinate `x`.  If the inner integral is `c · F(ι_T y)` for every `y` (the *line step*), then `∫_{U_{T∪{q}}} F = c · ∫_{U_T} F`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMeas
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitStep
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteSetFibre

open Classical

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInduction

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The integrand pulled back to the `S`-coordinates is integrable when `F` is. -/
theorem integrable_localPi (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (hint : Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    Integrable (fun a : WS S × WS S => globalIntegrand I Z gInf (iotaS S hS a.1, iotaS S hS a.2))
      ((localPi S).prod (localPi S)) := by
  have hmeas : Measurable
      (fun a : WS S × WS S => globalIntegrand I Z gInf (iotaS S hS a.1, iotaS S hS a.2)) := by
    have hi : Measurable (fun a : WS S × WS S => (iotaS S hS a.1, iotaS S hS a.2)) :=
      ((continuous_iotaS S hS).measurable.comp measurable_fst).prodMk
        ((continuous_iotaS S hS).measurable.comp measurable_snd)
    exact (globalIntegrand_measurable I Z hZ gInf).comp hi
  have hon := hint.integrableOn (s := UregionS S)
  have hcongr : IntegrableOn (fun z : FiniteAwayThree × FiniteAwayThree =>
      (fun a : WS S × WS S => globalIntegrand I Z gInf (iotaS S hS a.1, iotaS S hS a.2))
        (piS S z.1, piS S z.2)) (UregionS S) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
    hon.congr_fun (fun z hz => globalIntegrand_eq_iotaS I h hform S hS Z hZ gInf z hz)
      (UregionS_measurable S hS)
  have := (integrable_map_measure (μ := (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure).restrict (UregionS S))
    hmeas.aestronglyMeasurable (measurable_piPair S).aemeasurable).2 hcongr
  rwa [map_piS_prod_restrict_UregionS S hS] at this

/-- **Fubini step.** -/
theorem integral_union_eq (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree) (q : FinitePlace) (hq : q ≠ placeThree)
    (hqT : q ∉ T) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (hint : Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    ∫ z in UregionS (T ∪ {q}), globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      ∫ y : WS T × WS T, ∫ x : q.adicCompletion ℚ × q.adicCompletion ℚ,
        globalIntegrand I Z gInf (finiteAwayThreeAtPlace q hq x.1 + iotaS T hT y.1,
          finiteAwayThreeAtPlace q hq x.2 + iotaS T hT y.2)
          ∂((finiteCompletionMeasure q).prod (finiteCompletionMeasure q)) ∂((localPi T).prod (localPi T)) := by
  have hU : ∀ p ∈ T ∪ {q}, p ≠ placeThree := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact hT p hp
    · rw [Finset.mem_singleton.1 hp]; exact hq
  set F := globalIntegrand I Z gInf with hF
  set G : WS (T ∪ {q}) × WS (T ∪ {q}) → ℂ := fun a => F (iotaS (T ∪ {q}) hU a.1, iotaS (T ∪ {q}) hU a.2) with hG
  have hGint : Integrable G ((localPi (T ∪ {q})).prod (localPi (T ∪ {q}))) :=
    integrable_localPi I h hform (T ∪ {q}) hU Z hZ gInf hint
  let Φ : (WS T × q.adicCompletion ℚ) × (WS T × q.adicCompletion ℚ) ≃ᵐ
      WS (T ∪ {q}) × WS (T ∪ {q}) := MeasurableEquiv.prodCongr (psiU T q hqT) (psiU T q hqT)
  have hΦ : MeasurePreserving Φ (((localPi T).prod (finiteCompletionMeasure q)).prod
      ((localPi T).prod (finiteCompletionMeasure q))) ((localPi (T ∪ {q})).prod (localPi (T ∪ {q}))) :=
    (psiU_mp T q hqT).prod (psiU_mp T q hqT)
  let C4 : (WS T × WS T) × (q.adicCompletion ℚ × q.adicCompletion ℚ) ≃ᵐ
      (WS T × q.adicCompletion ℚ) × (WS T × q.adicCompletion ℚ) :=
    (comm4 : (WS T × q.adicCompletion ℚ) × (WS T × q.adicCompletion ℚ) ≃ᵐ
      (WS T × WS T) × (q.adicCompletion ℚ × q.adicCompletion ℚ)).symm
  have hC4 : MeasurePreserving C4 (((localPi T).prod (localPi T)).prod
      ((finiteCompletionMeasure q).prod (finiteCompletionMeasure q)))
      (((localPi T).prod (finiteCompletionMeasure q)).prod ((localPi T).prod (finiteCompletionMeasure q))) :=
    MeasurePreserving.symm _ (comm4_mp (localPi T) (finiteCompletionMeasure q) (localPi T) (finiteCompletionMeasure q))
  have hform2 : ∀ p : (WS T × WS T) × (q.adicCompletion ℚ × q.adicCompletion ℚ), G (Φ (C4 p)) =
      F (finiteAwayThreeAtPlace q hq p.2.1 + iotaS T hT p.1.1, finiteAwayThreeAtPlace q hq p.2.2 + iotaS T hT p.1.2) := by
    rintro ⟨⟨y1, y2⟩, ⟨x1, x2⟩⟩
    simp only [hG, Φ, C4]
    rw [show (comm4 : (WS T × q.adicCompletion ℚ) × (WS T × q.adicCompletion ℚ) ≃ᵐ
      (WS T × WS T) × (q.adicCompletion ℚ × q.adicCompletion ℚ)).symm ((y1, y2), (x1, x2)) = ((y1, x1), (y2, x2)) from rfl]
    show F (iotaS (T ∪ {q}) hU (psiU T q hqT (y1, x1)), iotaS (T ∪ {q}) hU (psiU T q hqT (y2, x2))) = _
    rw [iotaS_psiU T q hT hU hq hqT, iotaS_psiU T q hT hU hq hqT, add_comm (iotaS T hT y1), add_comm (iotaS T hT y2)]
  have hint2 : Integrable (G ∘ Φ ∘ C4) (((localPi T).prod (localPi T)).prod
      ((finiteCompletionMeasure q).prod (finiteCompletionMeasure q))) := by
    have h1 : Integrable (G ∘ Φ) (((localPi T).prod (finiteCompletionMeasure q)).prod
        ((localPi T).prod (finiteCompletionMeasure q))) :=
      (hΦ.integrable_comp_emb Φ.measurableEmbedding).2 hGint
    exact (hC4.integrable_comp_emb C4.measurableEmbedding).2 h1
  rw [finiteIntegral_eq_localPi I h hform (T ∪ {q}) hU Z hZ gInf]
  calc ∫ a, F (iotaS (T ∪ {q}) hU a.1, iotaS (T ∪ {q}) hU a.2) ∂((localPi (T ∪ {q})).prod (localPi (T ∪ {q})))
      = ∫ p, G (Φ (C4 p)) ∂(((localPi T).prod (localPi T)).prod
          ((finiteCompletionMeasure q).prod (finiteCompletionMeasure q))) := by
        rw [(hC4.integral_comp' (fun x => G (Φ x))), hΦ.integral_comp' G]
    _ = _ := by
        have := integral_prod (fun p : (WS T × WS T) × (q.adicCompletion ℚ × q.adicCompletion ℚ) => G (Φ (C4 p)))
          hint2
        rw [this]
        simp_rw [hform2]

/-- **The line step**: integrating the global integrand over the coordinate at a new place `q ∉ T` (the other coordinates `y` fixed) multiplies its value at
the point with coordinates `y` and `0` at `q` by the local constant `c`. -/
def LineStep (I : EichlerInput σ n) (Z : BinaryFiniteGL) (gInf : BinaryRealGL) (q : FinitePlace)
    (hq : q ≠ placeThree) (c : ℂ) : Prop :=
  ∀ (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree), q ∉ T → ∀ y : WS T × WS T,
    ∫ x : q.adicCompletion ℚ × q.adicCompletion ℚ,
        globalIntegrand I Z gInf (finiteAwayThreeAtPlace q hq x.1 + iotaS T hT y.1,
          finiteAwayThreeAtPlace q hq x.2 + iotaS T hT y.2)
          ∂((finiteCompletionMeasure q).prod (finiteCompletionMeasure q)) =
      c * globalIntegrand I Z gInf (iotaS T hT y.1, iotaS T hT y.2)

/-- From the line step, adjoining `q` multiplies the finite integral by `c`. -/
theorem integral_union_of_lineStep (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree) (q : FinitePlace) (hq : q ≠ placeThree)
    (hqT : q ∉ T) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (hint : Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))
    (c : ℂ) (hline : LineStep I Z gInf q hq c) :
    ∫ z in UregionS (T ∪ {q}), globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      c * ∫ z in UregionS T, globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  rw [integral_union_eq I h hform T hT q hq hqT Z hZ gInf hint, finiteIntegral_eq_localPi I h hform T hT Z hZ gInf,
    ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hline T hT hqT y)

/-- The base case: `∫_{U_∅} F = F(0,0)`. -/
theorem integral_empty (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) :
    ∫ z in UregionS (∅ : Finset FinitePlace), globalIntegrand I Z gInf z
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) = globalIntegrand I Z gInf (0, 0) := by
  have hS : ∀ p ∈ (∅ : Finset FinitePlace), p ≠ placeThree := fun p hp => absurd hp (Finset.notMem_empty p)
  rw [finiteIntegral_eq_localPi I h hform ∅ hS Z hZ gInf]
  have hpi : localPi (∅ : Finset FinitePlace) =
      Measure.dirac (default : ∀ p : (∅ : Finset FinitePlace), p.1.adicCompletion ℚ) := by
    rw [localPi, Measure.pi_of_empty]
    congr 1
  have hι : ∀ a : WS (∅ : Finset FinitePlace), iotaS ∅ hS a = 0 := fun a => by
    rw [iotaS_apply]; simp
  rw [hpi, Measure.dirac_prod_dirac, integral_dirac]
  simp [hι]

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInduction
