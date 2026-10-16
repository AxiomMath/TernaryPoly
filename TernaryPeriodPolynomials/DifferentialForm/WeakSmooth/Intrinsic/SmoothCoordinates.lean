module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothChartIntegral
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.ChartGeometry
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualPairing
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.HilbertRegularCurrent

@[expose] public section


/-! Exact literal Bochner coordinates for the actual intrinsic current of local smooth forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
open scoped Distributions

/-- The actual scalar chart coordinate of the genuine intrinsic smooth current is precisely the
actual scalar Haar current of the genuine raw local coefficient. -/
theorem intrinsicCurrentCoordinates_smooth (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (a : EquivariantForm (deckRepresentation n) (chartOpen S Ω) k) (i : Index n k) :
    intrinsicCurrentCoordinates n k S Ω hΩ
        (intrinsicSmoothCurrent n k (chartOpen S Ω) (chartOpen_isOpen S Ω.isOpen) a) i =
      scalarRegularCurrent volume Ω (components n k a.val.val i)
        (intrinsicChart_local_coefficient_continuous n k S Ω hΩ a i) := by
  apply LinearMap.ext
  intro φ
  let w := intrinsicMetricDualChartTest n k S Ω hΩ i φ
  apply (intrinsicSmoothPairing_integral_chart n k (chartOpen S Ω) a w S
    (metricDualChartTest_support n k S Ω hΩ i φ)).trans
  have hrep := congrArg (fun z : Form (F := Coefficients n) (quotientChart S).target k => z.val)
    (metricDualChartTest_representative n k S Ω hΩ i φ)
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply (congrArg (fun f : Coordinates → FormValue n k =>
    SymmetricSpaceRiemannian.coordinateDensity x * formPairing n k x (a.val.val x) (f x)) hrep).trans
  exact metricDualTestRaw_pairing_all n k Ω (hΩ.trans (quotientChart_target_subset S)) i φ (a.val.val x) x

/-- The genuine intrinsic current of a local smooth form is exactly the Bochner regular current
of its genuine local coordinate form, with actual Haar coordinate measure. -/
theorem intrinsicChartFormCurrent_smooth (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (a : EquivariantForm (deckRepresentation n) (chartOpen S Ω) k) :
    intrinsicChartFormCurrent n k S Ω hΩ
        (intrinsicSmoothCurrent n k (chartOpen S Ω) (chartOpen_isOpen S Ω.isOpen) a) =
      valuedRegularCurrent volume Ω a.val.val (intrinsicChart_local_smooth n k S Ω hΩ a).continuousOn := by
  apply (Function.LeftInverse.injective (formWeakOfCoordinates_coordinates n k Ω))
  funext i
  exact (congrFun (formWeakCoordinates_ofCoordinates n k Ω _) i).trans
    ((intrinsicCurrentCoordinates_smooth n k S Ω hΩ a i).trans
      (formWeakCoordinates_regular n k Ω _ _ i).symm)

end TernaryPoly.PolynomialFormWeakSmooth
