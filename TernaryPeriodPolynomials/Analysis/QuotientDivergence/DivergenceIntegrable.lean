module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.LocalizedDivergence
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.Support
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.VolumePositive

@[expose] public section

/-! Compactness and integrability of the actual descended divergence and partition terms. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  PolynomialCoefficientBundle SmoothCoveringDeRham PolynomialFormConnection SymmetricSpaceRiemannian Set MeasureTheory
open scoped ContDiff Manifold SymmetricSpaceRiemannian

theorem divergence_support (D : OrbitSpace → ℝ) (V : Coordinates → Coordinates)
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x) :
    Function.support D ⊆ projectedVectorSupport V := by
  intro q hq
  by_contra h
  apply hq
  have hx : coordinateChart (chosenLift q) ∈ positiveCoordinates := extract_mem _
  have hz := weightedDivergence_eq_zero_of_notMem_projected_support V _ hx
    (by simpa only [coordinateProjection_chosen, projectedVectorSupport] using h)
  exact (congrArg D (coordinateProjection_chosen q).symm).trans ((hD _ hx).trans hz)

theorem divergence_compact (D : OrbitSpace → ℝ) (V : Coordinates → Coordinates)
    (hK : IsCompact (projectedVectorSupport V))
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x) :
    HasCompactSupport D :=
  hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (divergence_support D V hD) isClosed_closure)

theorem localizedDivergence_compact (φ D : OrbitSpace → ℝ) (V : Coordinates → Coordinates)
    (hK : IsCompact (projectedVectorSupport V))
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x) :
    HasCompactSupport (localizedDivergence φ D V) :=
  ((divergence_compact D V hK hD).mul_left).add (directional_compact φ V hK)

theorem integrable_localizedDivergence (φ D : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (hDc : Continuous D)
    (V : Coordinates → Coordinates) (hVs : ContDiffOn ℝ ∞ V positiveCoordinates)
    (hVd : IsDeckVectorField V) (hK : IsCompact (projectedVectorSupport V))
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x) :
    Integrable (localizedDivergence φ D V) orbitVolume :=
  ((hφ.continuous.mul hDc).add (contMDiff_directional φ hφ V hVd hVs).continuous).integrable_of_hasCompactSupport
    (localizedDivergence_compact φ D V hK hD)

end TernaryPoly.QuotientScalarDescent
