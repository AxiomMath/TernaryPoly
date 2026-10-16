module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.DivergenceIntegrable
public import TernaryPeriodPolynomials.DifferentialForm.Connection.PartitionDerivative

@[expose] public section


/-! The genuine finite quotient partition has vanishing total directional correction. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  PolynomialCoefficientBundle SmoothCoveringDeRham SmoothDeRhamGluing PolynomialFormConnection Set Filter
open scoped ContDiff Manifold Topology

variable {ι : Type*} [Fintype ι]

theorem sum_directional_partition (φ : ι → OrbitSpace → ℝ)
    (hφ : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (φ i))
    (V : Coordinates → Coordinates) (hVs : ContDiffOn ℝ ∞ V positiveCoordinates)
    (hVd : IsDeckVectorField V)
    (hpart : ∀ q ∈ projectedVectorSupport V, ∑ i, φ i q = 1) (q : OrbitSpace) :
    ∑ i, directional (φ i) V q = 0 := by
  let x := coordinateChart (chosenLift q)
  have hx : x ∈ positiveCoordinates := extract_mem _
  have hp : coordinateProjection x = q := coordinateProjection_chosen q
  have hd (i : ι) : DifferentiableAt ℝ (liftScalar (φ i)) x :=
    ((liftScalar_contDiff (hφ i) x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have he : (∑ i, directional (φ i) V q) = ∑ i, fderiv ℝ (liftScalar (φ i)) x (V x) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (congrArg (directional (φ i) V) hp.symm).trans (directional_coordinateProjection (φ i) (hφ i) V hVd x hx)
  refine he.trans (finite_partition_derivative_cancel (fun i => liftScalar (φ i)) V x hd
    (hVs.continuousOn.continuousAt (isOpen_positiveCoordinates.mem_nhds hx)) ?_)
  apply Filter.Eventually.of_forall
  intro y hy
  exact hpart _ (subset_closure ⟨y,hy,rfl⟩)

theorem sum_localizedDivergence (φ : ι → OrbitSpace → ℝ)
    (hφ : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (φ i))
    (D : OrbitSpace → ℝ) (V : Coordinates → Coordinates)
    (hVs : ContDiffOn ℝ ∞ V positiveCoordinates) (hVd : IsDeckVectorField V)
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x)
    (hpart : ∀ q ∈ projectedVectorSupport V, ∑ i, φ i q = 1) (q : OrbitSpace) :
    ∑ i, localizedDivergence (φ i) D V q = D q := by
  simp only [localizedDivergence, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_directional_partition φ hφ V hVs hVd hpart q, add_zero]
  by_cases hz : D q = 0
  · rw [hz,mul_zero]
  · rw [hpart q (divergence_support D V hD hz),one_mul]

end TernaryPoly.QuotientScalarDescent
