module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.DivergencePartition
public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.FiniteChartPartition

@[expose] public section

/-! Global divergence integration for actual compactly supported quotient vector fields. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  SmoothCoveringDeRham PolynomialFormConnection PolynomialFormCoordinates SymmetricSpaceRiemannian Set MeasureTheory
open scoped ContDiff Manifold SymmetricSpaceRiemannian

theorem integral_divergence_eq_zero (V : Coordinates → Coordinates)
    (hVs : ContDiffOn ℝ ∞ V positiveCoordinates) (hVd : IsDeckVectorField V)
    (hK : IsCompact (projectedVectorSupport V)) (D : OrbitSpace → ℝ) (hDc : Continuous D)
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x) :
    ∫ q, D q ∂orbitVolume = 0 := by
  classical
  obtain ⟨s, φ, hsφ⟩ := exists_finite_chart_partition (projectedVectorSupport V) hK
  have hp : ∀ q ∈ projectedVectorSupport V, ∑ i : s, φ i q = 1 := by
    intro q hq
    simpa only [finsum_eq_sum_of_fintype] using φ.sum_eq_one hq
  have hi (i : s) : Integrable (localizedDivergence (φ i) D V) orbitVolume :=
    integrable_localizedDivergence (φ i) D (φ i).contMDiff hDc V hVs hVd hK hD
  calc
    _ = ∫ q, ∑ i : s, localizedDivergence (φ i) D V q ∂orbitVolume :=
      integral_congr_ae (Filter.Eventually.of_forall (fun q =>
        (sum_localizedDivergence (fun i : s => φ i) (fun i => (φ i).contMDiff) D V hVs hVd hD hp q).symm))
    _ = ∑ i : s, ∫ q, localizedDivergence (φ i) D V q ∂orbitVolume :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = 0 := Finset.sum_eq_zero (fun i _ =>
      integral_localizedDivergence i.val (φ i) D (φ i).contMDiff V hVs hVd hK (hsφ i) hD)

end TernaryPoly.QuotientScalarDescent
