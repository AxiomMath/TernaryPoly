module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LowCurrent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Regular

@[expose] public section

/-! Actual tangent and coefficient evaluation commute with genuine Bochner form currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open MeasureTheory PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts SmoothLocalDeRham

/-- Evaluation of a continuous actual one-form has continuous coefficient values. -/
theorem lowRegularEvaluation_continuous (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (f : Coordinates → FormValue n 1) (hf : ContinuousOn f Ω) (v : Coordinates) :
    ContinuousOn (fun x => (oneEquiv (E := Coordinates) (F := Coefficients n)).symm (f x) v) Ω :=
  ((oneEquiv (E := Coordinates) (F := Coefficients n)).symm.toContinuousLinearMap.continuous.comp_continuousOn hf).clm_apply continuousOn_const

/-- Evaluating an actual regular one-form current at an actual tangent vector gives the actual
regular current of the evaluated coefficient field. -/
theorem formWeakOneValue_regular (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (f : Coordinates → FormValue n 1) (hf : ContinuousOn f Ω) (v : Coordinates) :
    formWeakOneValue n Ω (valuedRegularCurrent volume Ω f hf) v =
      valuedRegularCurrent volume Ω (fun x => (oneEquiv (E := Coordinates) (F := Coefficients n)).symm (f x) v)
        (lowRegularEvaluation_continuous n Ω f hf v) := by
  apply LinearMap.ext
  intro φ
  let L : FormValue n 1 →L[ℝ] Coefficients n :=
    (ContinuousLinearMap.apply ℝ (Coefficients n) v).comp
      (oneEquiv (E := Coordinates) (F := Coefficients n)).symm.toContinuousLinearMap
  change L (∫ x, φ x • f x) = ∫ x, φ x • L (f x)
  calc
    _ = ∫ x, L (φ x • f x) :=
      (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (E := FormValue n 1)
        (Fₗ := Coefficients n) L (valuedRegular_test_integrable volume Ω f hf φ)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => L.map_smul (φ x) (f x)))

/-- Encoding a genuine regular scalar current as zero-forms gives the actual regular zero-form
current of the genuinely encoded coefficient function. -/
theorem zeroFormWeak_regular (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (f : Coordinates → Coefficients n) (hf : ContinuousOn f Ω) :
    zeroFormWeak n Ω (valuedRegularCurrent volume Ω f hf) =
      valuedRegularCurrent volume Ω (fun x => zeroEquiv (f x))
        ((zeroEquiv (E := Coordinates) (F := Coefficients n)).toContinuousLinearMap.continuous.comp_continuousOn hf) :=
  valuedRegularCurrent_comp (V := Coefficients n) (W := FormValue n 0) volume Ω
    (zeroEquiv (E := Coordinates) (F := Coefficients n)).toContinuousLinearMap f hf

end TernaryPoly.PolynomialFormWeakSmooth
