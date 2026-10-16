module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Differential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.RegularDerivative
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.RegularAlgebra

@[expose] public section


/-! The exterior differential of an actual smooth form current is its actual smooth differential. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts
open SmoothLocalDeRham ContinuousAlternatingMap
open scoped ContDiff

/-- Each true constant-symbol derivative coefficient of a smooth form is continuous. -/
theorem formSymbolDerivative_continuousOn (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (f : Coordinates → FormValue n k) (hf : ContDiffOn ℝ ∞ f Ω) (d : Fin 5) :
    ContinuousOn (fun x => symbol n k d (fderiv ℝ f x (Pi.single d 1))) Ω :=
  (symbol n k d).continuous.comp_continuousOn
    (valuedRegularDerivative_continuousOn Ω f hf (Pi.single d 1))

/-- The actual form-valued Bochner current intertwines genuine smooth exterior differentiation
with the genuine exterior-symbol weak differential. -/
theorem formWeakExterior_regular (n k : ℕ) (μ : Measure Coordinates) [IsAddHaarMeasure μ]
    (Ω : TopologicalSpace.Opens Coordinates) (f : Coordinates → FormValue n k)
    (hf : ContDiffOn ℝ ∞ f Ω) :
    formWeakExterior n k Ω (valuedRegularCurrent μ Ω f hf.continuousOn) =
      valuedRegularCurrent μ Ω (extDeriv f) (smooth_extDeriv Ω.isOpen hf).continuousOn := by
  have hd (d : Fin 5) :
      (symbol n k d).toLinearMap.comp
        (valuedWeakDerivative Ω (Pi.single d 1) (valuedRegularCurrent μ Ω f hf.continuousOn)) =
      valuedRegularCurrent μ Ω (fun x => symbol n k d (fderiv ℝ f x (Pi.single d 1)))
        (formSymbolDerivative_continuousOn n k Ω f hf d) :=
    (congrArg (fun T : FormWeak n k Ω => (symbol n k d).toLinearMap.comp T)
      (valuedRegularCurrent_derivative μ Ω f hf (Pi.single d 1))).trans
        (valuedRegularCurrent_comp (V := FormValue n k) (W := FormValue n (k+1)) μ Ω (symbol n k d)
          (fun x => fderiv ℝ f x (Pi.single d 1))
          (valuedRegularDerivative_continuousOn Ω f hf (Pi.single d 1)))
  apply (Finset.sum_congr rfl (fun d _ => hd d)).trans
  apply (valuedRegularCurrent_sum μ Ω Finset.univ
    (fun d x => symbol n k d (fderiv ℝ f x (Pi.single d 1)))
    (formSymbolDerivative_continuousOn n k Ω f hf)).symm.trans
  apply valuedRegularCurrent_congr μ Ω
  intro x _
  exact (extDeriv_symbol n k f x).symm

end TernaryPoly.PolynomialFormWeakSmooth
