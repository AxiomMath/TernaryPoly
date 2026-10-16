module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Current
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Coefficient

@[expose] public section


/-! Exact identification of actual smooth Hilbert chart currents with Bochner regular currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialFormCoordinates PolynomialFormMetric PolynomialCoefficientMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering PolynomialFormHilbert
  SmoothCoveringDeRham SmoothLocalDeRham

/-- Actual scalar form coordinates commute with the actual Bochner form current. -/
theorem formWeakCoordinates_regular (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (f : Coordinates → FormValue n k) (hf : ContinuousOn f Ω) (i : Index n k) :
    formWeakCoordinates n k Ω (valuedRegularCurrent volume Ω f hf) i =
      scalarRegularCurrent volume Ω (fun x => coordinates n k (f x) i)
        (((ContinuousLinearMap.proj i).comp (coordinates n k).toContinuousLinearMap).continuous.comp_continuousOn hf) :=
  valuedRegularCurrent_scalarCoefficient volume Ω
    ((ContinuousLinearMap.proj i).comp (coordinates n k).toContinuousLinearMap) f hf

/-- The genuine form-valued chart current of any actual smooth compact form is exactly the
Bochner current of its genuine chart representative, with actual coordinate Haar measure. -/
theorem chartHilbertFormCurrent_inclusion (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (w : Core n k) :
    chartHilbertFormCurrent n k S Ω hΩ (inclusion n k w) =
      valuedRegularCurrent volume Ω (globalChartRepresentative (deckRepresentation n) S k w.val).val
        ((Form.smooth (globalChartRepresentative (deckRepresentation n) S k w.val)).continuousOn.mono hΩ) := by
  apply (Function.LeftInverse.injective (formWeakOfCoordinates_coordinates n k Ω))
  funext i
  exact (congrFun (formWeakCoordinates_ofCoordinates n k Ω _) i).trans
    ((coordinateHilbertCurrent_inclusion n k S Ω hΩ i w).trans
      (formWeakCoordinates_regular n k Ω _ _ i).symm)

end TernaryPoly.PolynomialFormWeakSmooth
