module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SingleFiniteIntegral
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitShape
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitMeas

@[expose] public section


/-!
# Finite-set reduction of the finite integral (route (b), step (4') for general `S`)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a finite set `S` of places, `S ⊆ {places ≠ 3}`:

* `globalIntegrand_eq_iotaS`: on `U_S` the global integrand equals the global integrand at the point
  whose local coordinates are the `S`-coordinates of `z` and which vanishes off `S` (fibre comparison
  through `smooth_fibre_general`, with the local factorisations chosen at every place);
* `finiteIntegral_eq_localPi`: the integral over `U_S` equals the integral over `(WS S)²` against
  `localPi S ⊗ localPi S` of the global integrand at the `iotaS`-embedded point.

The second step uses `setIntegral_UregionS` and the measurability of the global integrand
(`GlobalLimitMeas.globalIntegrand_measurable`).
-/

open Classical Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMeas
open TernaryPeriodPolynomials.Argument.LatticeCounts.SingleSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.SingleFiniteIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteSetFibre

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The point with `S`-coordinates `a` lies in `U_S`. -/
theorem iota_mem_UregionS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree)
    (a b : WS S) : (iotaS S hS a, iotaS S hS b) ∈ UregionS S := by
  intro w hw
  rw [show awayVal (iotaS S hS a) = (iotaS S hS a).val from rfl,
    show awayVal (iotaS S hS b) = (iotaS S hS b).val from rfl,
    eval_iotaS_of_notMem S hS a w hw, eval_iotaS_of_notMem S hS b w hw]
  exact ⟨(OS w).zero_mem, (OS w).zero_mem⟩

/-- On `S`, the evaluation of the `S`-coordinate point is the `S`-coordinate of the original point. -/
theorem eval_iota_piS_of_mem (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree)
    (x : FiniteAwayThree) (w : FinitePlace) (hw : w ∈ S) :
    finiteEvaluation w (awayVal (iotaS S hS (piS S x))) = finiteEvaluation w (awayVal x) :=
  eval_iotaS_of_mem S hS (piS S x) ⟨w, hw⟩

/-- **Fibre comparison on `U_S`.** The global integrand at `z ∈ U_S` equals the global integrand at
the point with the same `S`-coordinates and zero off `S`. -/
theorem globalIntegrand_eq_iotaS (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (z : FiniteAwayThree × FiniteAwayThree) (hz : z ∈ UregionS S) :
    globalIntegrand I Z gInf z =
      globalIntegrand I Z gInf (iotaS S hS (piS S z.1), iotaS S hS (piS S z.2)) := by
  have hfam : ∀ w : FinitePlace, ∃ P κ : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ),
      P.val 2 0 = 0 ∧ P.val 2 1 = 0 ∧
        LstR (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2)) =
          P.val * κ.val ∧ IntGL3 w κ.val := by
    intro w
    obtain ⟨P0, κ0, hP20, hP21, hfac, hκ0⟩ :=
      plane_factor_all w (finiteCompletionPadicAddEquiv w (finiteEvaluation w (awayVal z.1)))
        (finiteCompletionPadicAddEquiv w (finiteEvaluation w (awayVal z.2)))
    rw [psiV_adic, psiV_adic] at hfac
    exact ⟨P0, κ0, hP20, hP21, hfac, hκ0⟩
  choose P κ hP20 hP21 hfac hκ using hfam
  unfold globalIntegrand
  refine smooth_fibre_general I h hform S P κ P κ
    (fun w _ => ⟨hP20 w, hP21 w⟩) (fun w _ => ⟨hP20 w, hP21 w⟩)
    (LfinGLof (awayVal z.1) (awayVal z.2))
    (LfinGLof (awayVal (iotaS S hS (piS S z.1))) (awayVal (iotaS S hS (piS S z.2))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ Z hZ gInf
  · intro w _
    rw [evM3_LfinGLof]
    exact hfac w
  · intro w _
    exact hκ w
  · intro w hw
    exact intGL3_LfinGLof_of_mem hz w hw
  · intro w hw
    rw [evM3_LfinGLof, eval_iota_piS_of_mem S hS z.1 w hw, eval_iota_piS_of_mem S hS z.2 w hw]
    exact hfac w
  · intro w _
    exact hκ w
  · intro w hw
    exact intGL3_LfinGLof_of_mem (iota_mem_UregionS S hS _ _) w hw
  · intro w _
    rfl

/-- **Reduction to the `S`-local coordinates.** The integral over `U_S` equals the integral over
`(WS S)²` against `localPi S ⊗ localPi S` of the global integrand at the `iotaS`-embedded point. -/
theorem finiteIntegral_eq_localPi (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) :
    ∫ z in UregionS S, globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      ∫ a, globalIntegrand I Z gInf (iotaS S hS a.1, iotaS S hS a.2)
        ∂((localPi S).prod (localPi S)) := by
  have hmeas : Measurable
      (fun a : WS S × WS S => globalIntegrand I Z gInf (iotaS S hS a.1, iotaS S hS a.2)) := by
    have hi : Measurable (fun a : WS S × WS S => (iotaS S hS a.1, iotaS S hS a.2)) :=
      ((continuous_iotaS S hS).measurable.comp measurable_fst).prodMk
        ((continuous_iotaS S hS).measurable.comp measurable_snd)
    exact (globalIntegrand_measurable I Z hZ gInf).comp hi
  have hcongr : ∫ z in UregionS S, globalIntegrand I Z gInf z
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      ∫ z in UregionS S,
        globalIntegrand I Z gInf (iotaS S hS (piS S z.1), iotaS S hS (piS S z.2))
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
    setIntegral_congr_fun (UregionS_measurable S hS)
      (fun z hz => globalIntegrand_eq_iotaS I h hform S hS Z hZ gInf z hz)
  rw [hcongr]
  exact setIntegral_UregionS S hS
    (fun a => globalIntegrand I Z gInf (iotaS S hS a.1, iotaS S hS a.2))
    hmeas.aestronglyMeasurable

end TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteSetFibre

end
