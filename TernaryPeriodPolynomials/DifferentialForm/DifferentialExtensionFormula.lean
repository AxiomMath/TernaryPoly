module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Differential
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Locality
public import TernaryPeriodPolynomials.Analysis.Finite.FirstOrderSupport

@[expose] public section



/-! Compact coefficient extensions represent the genuine exterior derivative on supported forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration
open scoped ContDiff

theorem extDeriv_eq_extended_matrix (n k : ℕ) (K : Set Coordinates)
    (a : Index n (k+1) → Index n k → Fin 5 → Coordinates → ℝ)
    (he : ∀ x ∈ K, ∀ j i d, a j i d x = differentialCoefficients n k j i d x)
    (w : Coordinates → FormValue n k) (hw : ContDiff ℝ ∞ w) (hsw : tsupport w ⊆ K)
    (j : Index n (k+1)) :
    components n (k+1) (extDeriv w) j =
      matrixFirstOrder (fun d : Fin 5 => (Pi.single d 1 : Coordinates)) a (fun _ _ _ _ => 0)
        (components n k w) j := by
  funext x
  by_cases hx : x ∈ K
  · apply (extDeriv_eq_matrixFirstOrder n k w (hw.differentiable (by simp) x) j).trans
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro d _
    simp only [firstOrder, he x hx j i d]
  · have hl : components n (k+1) (extDeriv w) j x = 0 := by
      change coordinates n (k+1) (extDeriv w x) j = 0
      rw [extDeriv_eq_zero_of_notMem_tsupport n k w (fun h => hx (hsw h)),
        ContinuousLinearEquiv.map_zero]
      rfl
    have hr := image_eq_zero_of_notMem_tsupport
      (f := matrixFirstOrder (fun d : Fin 5 => (Pi.single d 1 : Coordinates)) a (fun _ _ _ _ => 0)
        (components n k w) j)
      (fun h => hx (hsw (tsupport_matrixFirstOrder_subset _ _ _ _ (isClosed_tsupport w)
        (fun i => tsupport_components n k w i) j h)))
    exact hl.trans hr.symm

end TernaryPoly.PolynomialFormCoordinates
