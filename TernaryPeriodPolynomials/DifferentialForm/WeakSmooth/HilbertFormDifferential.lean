module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Differential

@[expose] public section

noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts
open scoped Distributions

/-- Genuine finite coordinates determine the actual exterior differential equation for every
maximal Hilbert graph pair. -/
theorem chartHilbertFormCurrent_differential (n k : ℕ) (S : SymmetricSpacePositive.Space)
    (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (SymmetricSpaceCovering.quotientChart S).target)
    (u : PolynomialFormHilbert.Hilbert n k) (z : PolynomialFormHilbert.Hilbert n (k+1))
    (h : (u,z) ∈ (PolynomialFormHilbert.maximalDifferential n k).graph) :
    formWeakExterior n k Ω (chartHilbertFormCurrent n k S Ω hΩ u) =
      chartHilbertFormCurrent n (k+1) S Ω hΩ z := by
  apply (Function.LeftInverse.injective (formWeakOfCoordinates_coordinates n (k+1) Ω))
  funext j
  have hu : formWeakCoordinates n k Ω (chartHilbertFormCurrent n k S Ω hΩ u) =
      fun i => coordinateHilbertCurrent n k S Ω hΩ i u := formWeakCoordinates_ofCoordinates n k Ω _
  have hz : formWeakCoordinates n (k+1) Ω (chartHilbertFormCurrent n (k+1) S Ω hΩ z) =
      fun i => coordinateHilbertCurrent n (k+1) S Ω hΩ i z := formWeakCoordinates_ofCoordinates n (k+1) Ω _
  exact (formWeakCoordinates_exterior n k Ω _ j).trans
    ((congrArg (fun w : Index n k → ScalarWeak Ω =>
      ∑ i : Index n k, ∑ d : Fin 5, symbolMatrix n k d j i •
        scalarWeakDerivative Ω (Pi.single d 1) (w i)) hu).trans
      ((maximal_graph_coordinate_differential n k S Ω hΩ u z h j).symm.trans
        (congrFun hz j).symm))

end TernaryPoly.PolynomialFormWeakSmooth
