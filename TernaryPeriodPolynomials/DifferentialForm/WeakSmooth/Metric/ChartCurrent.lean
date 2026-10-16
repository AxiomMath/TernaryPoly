module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.ChartTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualPairing
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Dual
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Inner

@[expose] public section


/-! Genuine Hilbert test currents in coordinates, using the actual inverse weighted Gram tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
  SmoothLocalDeRham SmoothCoveringDeRham CompactCoordinateIntegration
open scoped Distributions SymmetricSpaceRiemannian

/-- The actual coefficient current of a global algebraic compact-form functional in a genuine chart. -/
def coordinateTestCurrent (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) (i : Index n k) :
    TestDual n k →ₗ[ℝ] ScalarWeak Ω := (metricDualChartTest n k S Ω hΩ i).dualMap

/-- The genuine Hilbert coefficient current, defined by actual compact quotient test pairing. -/
def coordinateHilbertCurrent (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) (i : Index n k) :
    Hilbert n k →ₗ[ℝ] ScalarWeak Ω := (coordinateTestCurrent n k S Ω hΩ i).comp (hilbertTest n k)

@[simp] theorem coordinateHilbertCurrent_apply (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i : Index n k) (u : Hilbert n k) (φ : 𝓓(Ω, ℝ)) :
    coordinateHilbertCurrent n k S Ω hΩ i u φ =
      inner ℝ u (inclusion n k (metricDualChartTest n k S Ω hΩ i φ)) := rfl

/-- Actual smooth chart coefficients are continuous on the scalar-test domain. -/
theorem chartCoefficient_continuous (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) (i : Index n k)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    ContinuousOn (components n k (globalChartRepresentative (deckRepresentation n) S k w).val i) Ω :=
  (contDiffOn_components n k (Form.smooth (globalChartRepresentative (deckRepresentation n) S k w)) i).continuousOn.mono hΩ

/-- On every actual smooth compact form, the genuine Hilbert coordinate current is exactly
integration against its genuine coefficient, with the actual coordinate Haar measure. -/
theorem coordinateHilbertCurrent_inclusion (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i : Index n k) (w : Core n k) :
    coordinateHilbertCurrent n k S Ω hΩ i (inclusion n k w) =
      scalarRegularCurrent volume Ω
        (components n k (globalChartRepresentative (deckRepresentation n) S k w.val).val i)
        (chartCoefficient_continuous n k S Ω hΩ i w.val) := by
  apply LinearMap.ext
  intro φ
  change inner ℝ (inclusion n k w) (inclusion n k (metricDualChartTest n k S Ω hΩ i φ)) = _
  apply (inner_inclusion_chart_right n k S w (metricDualChartTest n k S Ω hΩ i φ)
    (metricDualChartTest_support n k S Ω hΩ i φ)).trans
  have hrep : (globalChartRepresentative (deckRepresentation n) S k
      (metricDualChartTest n k S Ω hΩ i φ).val).val = metricDualTestRaw n k Ω i φ :=
    congrArg (fun b : Form (F := Coefficients n) (quotientChart S).target k => b.val)
      (metricDualChartTest_representative n k S Ω hΩ i φ)
  apply (congrArg (fun b : Coordinates → FormValue n k => ∫ x, weightedPairing (weightedGram n k)
    (components n k (globalChartRepresentative (deckRepresentation n) S k w.val).val)
    (components n k b) x) hrep).trans
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact (weightedPairing_components n k _ _ x).trans
    (metricDualTestRaw_pairing_all n k Ω (hΩ.trans (quotientChart_target_subset S)) i φ _ x)

end TernaryPoly.PolynomialFormWeakSmooth
