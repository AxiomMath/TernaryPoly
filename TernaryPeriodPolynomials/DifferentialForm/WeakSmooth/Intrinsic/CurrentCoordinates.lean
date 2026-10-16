module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.TestCoordinates
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.TestSpanning
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.ScalarWeak

@[expose] public section


/-! Exact intrinsic local currents and their actual scalar compact-test coordinates. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
  SmoothCoveringDeRham
open scoped Distributions

/-- Actual scalar coordinates of an intrinsic local current are its actual inverse-Gram test pairings. -/
def intrinsicCurrentCoordinates (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (T : IntrinsicCurrent n k (chartOpen S Ω)) (i : Index n k) : ScalarWeak Ω :=
  T.comp (intrinsicMetricDualChartTest n k S Ω hΩ i)

/-- Reconstruct an intrinsic current from actual scalar coordinate currents using the actual
weighted-Gram coefficient tests of each genuine compact quotient test. -/
def intrinsicCurrentOfCoordinates (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (w : Index n k → ScalarWeak Ω) : IntrinsicCurrent n k (chartOpen S Ω) :=
  ∑ i : Index n k, (w i).comp (intrinsicMetricCoefficientTest n k S Ω i)

/-- Actual coordinate extraction is the left inverse of intrinsic-current reconstruction. -/
theorem intrinsicCurrentCoordinates_ofCoordinates (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (w : Index n k → ScalarWeak Ω) :
    intrinsicCurrentCoordinates n k S Ω hΩ (intrinsicCurrentOfCoordinates n k S Ω w) = w := by
  funext i
  apply LinearMap.ext
  intro φ
  change (∑ j : Index n k, (w j).comp (intrinsicMetricCoefficientTest n k S Ω j))
    (intrinsicMetricDualChartTest n k S Ω hΩ i φ) = w i φ
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, intrinsicMetricCoefficientTest_basis]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Genuine compact-test spanning makes intrinsic-current reconstruction a right inverse too. -/
theorem intrinsicCurrentOfCoordinates_coordinates (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (T : IntrinsicCurrent n k (chartOpen S Ω)) :
    intrinsicCurrentOfCoordinates n k S Ω (intrinsicCurrentCoordinates n k S Ω hΩ T) = T := by
  apply LinearMap.ext
  intro w
  change (∑ i : Index n k, (intrinsicCurrentCoordinates n k S Ω hΩ T i).comp
    (intrinsicMetricCoefficientTest n k S Ω i)) w = T w
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, intrinsicCurrentCoordinates]
  exact (map_sum T (fun i => intrinsicMetricDualChartTest n k S Ω hΩ i
    (intrinsicMetricCoefficientTest n k S Ω i w)) Finset.univ).symm.trans
      (congrArg T (intrinsicMetricCoefficient_reconstruct_supported n k S Ω hΩ w))

end TernaryPoly.PolynomialFormWeakSmooth
