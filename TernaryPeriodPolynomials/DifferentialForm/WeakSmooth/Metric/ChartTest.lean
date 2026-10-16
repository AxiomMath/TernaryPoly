module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualTest
public import TernaryPeriodPolynomials.Analysis.Compact.ChartExtension
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic

@[expose] public section


/-! Actual inverse-metric coordinate tests extended to genuine compact quotient forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric PolynomialFormHilbert
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
open scoped ContDiff Distributions

/-- A scalar coordinate test determines a genuine local coefficient form by the inverse weighted Gram matrix. -/
def metricDualChartForm (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) (i : Index n k) :
    𝓓(Ω, ℝ) →ₗ[ℝ] Form (F := Coefficients n) (quotientChart S).target k where
  toFun φ := ⟨metricDualTestRaw n k Ω i φ,
    (metricDualTestRaw_smooth n k Ω (hΩ.trans (quotientChart_target_subset S)) i φ).contDiffOn,
    by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hΩ (φ.tsupport_subset (metricDualTestRaw_tsupport n k Ω i φ ht))))⟩
  map_add' φ ψ := by
    apply Form.ext
    intro x _
    change (φ x + ψ x) • metricDualTestVector n k i x =
      φ x • metricDualTestVector n k i x + ψ x • metricDualTestVector n k i x
    exact (inferInstance : Module ℝ (FormValue n k)).add_smul _ _ _
  map_smul' c φ := by
    apply Form.ext
    intro x _
    change (c * φ x) • metricDualTestVector n k i x = c • (φ x • metricDualTestVector n k i x)
    exact (inferInstance : Module ℝ (FormValue n k)).mul_smul _ _ _

/-- The actual compact quotient test: extend through true deck sheets and then globally by zero. -/
def metricDualChartTest (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target) (i : Index n k) :
    𝓓(Ω, ℝ) →ₗ[ℝ] Core n k where
  toFun φ := compactChartExtend (deckRepresentation n) S (metricDualChartForm n k S Ω hΩ i φ)
    (metricDualTestRaw_hasCompactSupport n k Ω i φ)
    ((metricDualTestRaw_tsupport n k Ω i φ).trans (φ.tsupport_subset.trans hΩ))
  map_add' φ ψ := by
    apply Subtype.ext
    apply Subtype.ext
    apply Form.ext
    intro x _
    exact congrArg (fun w : EquivariantForm (deckRepresentation n) (quotientChart S).source k =>
      w.val.val x) (((chartExtend (deckRepresentation n) S k).comp
        (metricDualChartForm n k S Ω hΩ i)).map_add φ ψ)
  map_smul' c φ := by
    apply Subtype.ext
    apply Subtype.ext
    apply Form.ext
    intro x _
    exact congrArg (fun w : EquivariantForm (deckRepresentation n) (quotientChart S).source k =>
      w.val.val x) (((chartExtend (deckRepresentation n) S k).comp
        (metricDualChartForm n k S Ω hΩ i)).map_smul c φ)

/-- The genuine chart representative recovers the actual inverse-metric coordinate test exactly. -/
theorem metricDualChartTest_representative (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) :
    globalChartRepresentative (deckRepresentation n) S k (metricDualChartTest n k S Ω hΩ i φ).val =
      metricDualChartForm n k S Ω hΩ i φ :=
  globalChartRepresentative_compactChartExtend (deckRepresentation n) S
    (metricDualChartForm n k S Ω hΩ i φ)
    (metricDualTestRaw_hasCompactSupport n k Ω i φ)
    ((metricDualTestRaw_tsupport n k Ω i φ).trans (φ.tsupport_subset.trans hΩ))

/-- The compact quotient test has support inside the actual chart source. -/
theorem metricDualChartTest_support (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) :
    quotientSupport (metricDualChartTest n k S Ω hΩ i φ).val ⊆ (quotientChart S).source := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := quotientSupport_compactChartExtend (deckRepresentation n) S
    (metricDualChartForm n k S Ω hΩ i φ)
    (metricDualTestRaw_hasCompactSupport n k Ω i φ)
    ((metricDualTestRaw_tsupport n k Ω i φ).trans (φ.tsupport_subset.trans hΩ)) hq
  exact (quotientChart S).map_target (hΩ (φ.tsupport_subset (metricDualTestRaw_tsupport n k Ω i φ hx)))

end TernaryPoly.PolynomialFormWeakSmooth
