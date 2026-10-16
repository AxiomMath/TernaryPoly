module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LowDifferential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LowRegular
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Recognition

@[expose] public section


/-! Genuine smooth recognition of actual zero-form currents with smooth exterior derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialFormCoordinates PolynomialFormMetric PolynomialCoefficientMetric
  SymmetricSpaceCharts SmoothLocalDeRham
open scoped ContDiff

/-- The actual coefficient gradient of a zero-form current is its actual exterior derivative,
read as a coefficient-valued one-form. -/
theorem formWeakZeroValue_gradient (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (T : FormWeak n 0 Ω) :
    valuedWeakGradient Ω (formWeakZeroValue n Ω T) =
      formWeakOneValue n Ω (formWeakExterior n 0 Ω T) :=
  (formWeakExterior_zero n Ω (formWeakZeroValue n Ω T)).symm.trans
    (congrArg (fun W : FormWeak n 0 Ω => formWeakOneValue n Ω (formWeakExterior n 0 Ω W))
      (zeroFormWeak_zeroValue n Ω T))

/-- An actual zero-form compact-test current on an actual coordinate box whose actual exterior
derivative is a genuine smooth one-form is itself a genuine smooth zero-form current. -/
theorem coordinateTestBox_zeroForm_smooth_of_smooth_exterior (n : ℕ)
    (b : WeakCubeFive ≃L[ℝ] Coordinates) (c : Coordinates)
    (T : FormWeak n 0 (coordinateTestBox b c))
    (a : Coordinates → FormValue n 1) (ha : ContDiffOn ℝ ∞ a (coordinateTestBox b c))
    (hT : formWeakExterior n 0 (coordinateTestBox b c) T =
      valuedRegularCurrent volume (coordinateTestBox b c) a ha.continuousOn) :
    ∃ (f : Coordinates → FormValue n 0) (hf : ContDiffOn ℝ ∞ f (coordinateTestBox b c)),
      T = valuedRegularCurrent volume (coordinateTestBox b c) f hf.continuousOn := by
  let Ω := coordinateTestBox b c
  let e : Coefficients n ≃L[ℝ] (Index n 0 → ℝ) :=
    (zeroEquiv (E := Coordinates) (F := Coefficients n)).toContinuousLinearEquiv.trans (coordinates n 0)
  let A : Coordinates → Coordinates →L[ℝ] Coefficients n := fun x => (oneEquiv (E := Coordinates) (F := Coefficients n)).symm (a x)
  have hA : ContDiffOn ℝ ∞ A Ω := (oneEquiv (E := Coordinates) (F := Coefficients n)).symm.toContinuousLinearMap.contDiff.comp_contDiffOn ha
  have hgrad (v : Coordinates) : valuedWeakDerivative Ω v (formWeakZeroValue n Ω T) =
      valuedRegularCurrent volume Ω (fun x => A x v) (hA.continuousOn.clm_apply continuousOn_const) := by
    apply (congrArg (fun W : Coordinates →ₗ[ℝ] ValuedWeak (V := Coefficients n) Ω => W v)
      (formWeakZeroValue_gradient n Ω T)).trans
    exact (congrArg (fun W : FormWeak n 1 Ω => formWeakOneValue n Ω W v) hT).trans
      (formWeakOneValue_regular n Ω a ha.continuousOn v)
  obtain ⟨g, hg, hrep⟩ := coordinateTestBox_valued_smooth_of_smooth_gradient volume e b c
    (formWeakZeroValue n Ω T) A hA hgrad
  refine ⟨fun x => zeroEquiv (g x), (zeroEquiv (E := Coordinates) (F := Coefficients n)).toContinuousLinearMap.contDiff.comp_contDiffOn hg, ?_⟩
  exact (zeroFormWeak_zeroValue n Ω T).symm.trans
    ((congrArg (zeroFormWeak n Ω) hrep).trans (zeroFormWeak_regular n Ω g hg.continuousOn))

end TernaryPoly.PolynomialFormWeakSmooth
