module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Coefficient
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.SmoothRecognition

@[expose] public section


/-! Smooth-gradient recognition for actual coefficient-valued compact-test currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure SymmetricSpaceCharts
open scoped ContDiff Distributions
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Fintype I]

/-- A genuine vector-valued current with a genuine smooth gradient on an actual coordinate box
is represented there by a genuine smooth coefficient-valued function. -/
theorem coordinateTestBox_valued_smooth_of_smooth_gradient
    (μ : Measure Coordinates) [IsAddHaarMeasure μ]
    (e : V ≃L[ℝ] (I → ℝ)) (b : WeakCubeFive ≃L[ℝ] Coordinates) (c : Coordinates)
    (T : ValuedWeak (V := V) (coordinateTestBox b c))
    (a : Coordinates → Coordinates →L[ℝ] V)
    (ha : ContDiffOn ℝ ∞ a (coordinateTestBox b c))
    (hT : ∀ v, valuedWeakDerivative (coordinateTestBox b c) v T =
      valuedRegularCurrent μ (coordinateTestBox b c) (fun x => a x v)
        (ha.continuousOn.clm_apply continuousOn_const)) :
    ∃ (f : Coordinates → V) (hf : ContDiffOn ℝ ∞ f (coordinateTestBox b c)),
      T = valuedRegularCurrent μ (coordinateTestBox b c) f hf.continuousOn := by
  let Ω := coordinateTestBox b c
  let L (i : I) : V →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hex (i : I) : ∃ (g : Coordinates → ℝ) (hg : ContDiffOn ℝ ∞ g Ω),
      (L i).toLinearMap.comp T = scalarRegularCurrent μ Ω g hg.continuousOn := by
    have hai : ContDiffOn ℝ ∞ (fun x => (L i).comp (a x)) Ω := contDiffOn_const.clm_comp ha
    apply coordinateTestBox_smooth_of_smooth_gradient μ b c ((L i).toLinearMap.comp T)
      (fun x => (L i).comp (a x)) hai
    intro v
    change valuedWeakDerivative Ω v ((L i).toLinearMap.comp T) = _
    exact (valuedWeakDerivative_comp Ω (L i).toLinearMap v T).trans
      ((congrArg (fun U : ValuedWeak (V := V) Ω => (L i).toLinearMap.comp U) (hT v)).trans
        (valuedRegularCurrent_scalarCoefficient μ Ω (L i) (fun x => a x v) _))
  choose g hg hrep using hex
  let f : Coordinates → V := fun x => e.symm (fun i => g i x)
  have hf : ContDiffOn ℝ ∞ f Ω :=
    e.symm.toContinuousLinearMap.contDiff.comp_contDiffOn (contDiffOn_pi.mpr hg)
  refine ⟨f, hf, ?_⟩
  apply LinearMap.ext
  intro φ
  apply e.injective
  funext i
  have hi := LinearMap.congr_fun (hrep i) φ
  have hreg := LinearMap.congr_fun (valuedRegularCurrent_scalarCoefficient μ Ω (L i) f hf.continuousOn) φ
  change e (T φ) i = _ at hi
  change e (valuedRegularCurrent μ Ω f hf.continuousOn φ) i = _ at hreg
  apply hi.trans
  apply Eq.trans _ hreg.symm
  apply LinearMap.congr_fun
  apply scalarRegularCurrent_congr μ Ω
  intro x _
  exact (congrFun (e.apply_symm_apply (fun j => g j x)) i).symm

end TernaryPoly.PolynomialFormWeakSmooth
