module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.AdjointTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.ChartTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CompactChartSum
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Adjoint

@[expose] public section


/-! Exact compact quotient adjoint identity on actual inverse-weighted-Gram scalar tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric PolynomialFormHilbert
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
open scoped Distributions

/-- The genuine compact formal adjoint of an actual inverse-Gram chart test is exactly the
finite sum of lower-degree actual inverse-Gram chart tests of scalar transpose derivatives. -/
theorem compactAdjoint_metricDualChartTest (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (j : Index n (k + 1)) (φ : 𝓓(Ω, ℝ)) :
    compactAdjoint n k (metricDualChartTest n (k + 1) S Ω hΩ j φ) =
      ∑ i : Index n k, metricDualChartTest n k S Ω hΩ i
        (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
          (fun j i d => symbolMatrix n k d j i) j φ i) := by
  let t (i : Index n k) := metricDualChartTest n k S Ω hΩ i
    (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
      (fun j i d => symbolMatrix n k d j i) j φ i)
  have ht (i : Index n k) : quotientSupport (t i).val ⊆ (quotientChart S).source :=
    metricDualChartTest_support n k S Ω hΩ i _
  apply Subtype.ext
  apply eq_of_globalChartRepresentative_eq (deckRepresentation n) S
  · exact (quotientSupport_equivariantAdjoint n k _).trans (metricDualChartTest_support n (k+1) S Ω hΩ j φ)
  · exact quotientSupport_compact_sum (deckRepresentation n) k Finset.univ t _ (fun i _ => ht i)
  · apply Form.ext
    intro x _
    have hadj := globalChartRepresentative_compactAdjoint n k S
      (metricDualChartTest n (k+1) S Ω hΩ j φ) (metricDualChartTest_support n (k+1) S Ω hΩ j φ)
    have hrep : (globalChartRepresentative (deckRepresentation n) S (k+1)
        (metricDualChartTest n (k+1) S Ω hΩ j φ).val).val = metricDualTestRaw n (k+1) Ω j φ :=
      congrArg (fun b : Form (F := Coefficients n) (quotientChart S).target (k+1) => b.val)
        (metricDualChartTest_representative n (k+1) S Ω hΩ j φ)
    have hleft : (globalChartRepresentative (deckRepresentation n) S k
        (compactAdjoint n k (metricDualChartTest n (k+1) S Ω hΩ j φ)).val).val x =
        localAdjoint n k (metricDualTestRaw n (k+1) Ω j φ) x :=
      congrFun hadj x |>.trans (congrArg (fun w => localAdjoint n k w x) hrep)
    apply hleft.trans
    apply (congrFun (localAdjoint_metricDualTestRaw n k Ω
      (hΩ.trans (quotientChart_target_subset S)) j φ) x).trans
    symm
    apply (compactChartRepresentative_sum_apply (deckRepresentation n) S k Finset.univ t x).trans
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun b : Form (F := Coefficients n) (quotientChart S).target k => b.val x)
      (metricDualChartTest_representative n k S Ω hΩ i _)

end TernaryPoly.PolynomialFormWeakSmooth
