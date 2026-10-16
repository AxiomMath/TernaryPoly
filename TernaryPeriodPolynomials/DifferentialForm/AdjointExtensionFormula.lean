module

public import TernaryPeriodPolynomials.DifferentialForm.AdjointFirstOrder
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Support
public import TernaryPeriodPolynomials.Analysis.Finite.FirstOrderSupport
public import TernaryPeriodPolynomials.Analysis.Finite.FirstOrderReindex

@[expose] public section


/-! Actual adjoint components equal a globally extended finite first-order expression on compact inputs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration
open scoped ContDiff

theorem localAdjoint_eq_extended_matrix (n k : ℕ) (K : Set Coordinates) (hKpos : K ⊆ positiveCoordinates)
    (a b : Index n k → Index n (k+1) → Index n k → Index n (k+1) → Fin 5 → Coordinates → ℝ)
    (he : ∀ x ∈ K, ∀ i t l j d,
      a i t l j d x = adjointFirstCoefficient n k i t l j d x ∧
      b i t l j d x = adjointZeroCoefficient n k i t l j d x)
    (w : Coordinates → FormValue n (k+1)) (hw : ContDiff ℝ ∞ w) (hsw : tsupport w ⊆ K) (i : Index n k) :
    components n k (localAdjoint n k w) i =
      matrixFirstOrder (fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates))
        (fun i t q => a i t q.1 q.2.1 q.2.2) (fun i t q => b i t q.1 q.2.1 q.2.2)
        (components n (k+1) w) i := by
  funext x
  by_cases hx : x ∈ K
  · apply (localAdjoint_firstOrder_expansion n k w x (hKpos hx) (hw.differentiable (by simp) x) i).trans
    apply Eq.trans ?_ (matrixFirstOrder_three_indices
      (fun d : Fin 5 => (Pi.single d 1 : Coordinates)) a b (components n (k+1) w) i x).symm
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro t _
    simp only [firstOrder, (he x hx i t l j d).1, (he x hx i t l j d).2]
  · have hl := image_eq_zero_of_notMem_tsupport (f := components n k (localAdjoint n k w) i)
      (fun h => hx (hsw ((tsupport_localAdjoint n k w) ((tsupport_components n k (localAdjoint n k w) i) h))))
    have hr := image_eq_zero_of_notMem_tsupport
      (f := matrixFirstOrder (fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates))
        (fun i t q => a i t q.1 q.2.1 q.2.2) (fun i t q => b i t q.1 q.2.1 q.2.2)
        (components n (k+1) w) i)
      (fun h => hx (hsw (tsupport_matrixFirstOrder_subset _ _ _ _ (isClosed_tsupport w)
        (fun t => tsupport_components n (k+1) w t) i h)))
    exact hl.trans hr.symm

end TernaryPoly.PolynomialFormCoordinates
