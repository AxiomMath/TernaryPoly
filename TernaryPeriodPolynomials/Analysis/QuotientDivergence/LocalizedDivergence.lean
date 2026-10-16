module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.DirectionalSupport
public import TernaryPeriodPolynomials.Analysis.Compact.VectorDivergence
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.Product
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.ChartIntegral

@[expose] public section

/-! Integration of one actual chart-localized current on the quotient. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  SmoothCoveringDeRham SmoothDeRhamGluing PolynomialFormConnection SymmetricSpaceRiemannian Set Filter MeasureTheory
open scoped ContDiff Manifold Topology SymmetricSpaceRiemannian

def localizedDivergence (φ D : OrbitSpace → ℝ) (V : Coordinates → Coordinates) (q : OrbitSpace) : ℝ :=
  φ q * D q + directional φ V q

theorem localizedDivergence_support (φ D : OrbitSpace → ℝ) (V : Coordinates → Coordinates) :
    Function.support (localizedDivergence φ D V) ⊆ tsupport φ := by
  intro q hq
  by_contra h
  apply hq
  have hd : directional φ V q = 0 := by
    by_contra hd
    exact h (directional_support_scalar φ V hd)
  simp only [localizedDivergence, image_eq_zero_of_notMem_tsupport h, hd, zero_mul, add_zero]

theorem localizedDivergence_coordinate (S : Space) (φ D : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (V : Coordinates → Coordinates)
    (hVs : ContDiffOn ℝ ∞ V positiveCoordinates) (hVd : IsDeckVectorField V)
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x)
    (x : Coordinates) (hx : x ∈ (quotientChart S).target) :
    localizedDivergence φ D V (coordinateProjection x) = weightedDivergence (localizedVector S φ V) x := by
  have hp := quotientChart_target_subset S hx
  have he : localizedVector S φ V =ᶠ[𝓝 x] (fun y => liftScalar φ y • V y) := by
    filter_upwards [(quotientChart S).open_target.mem_nhds hx] with y hy
    exact localizedVector_apply S φ V y hy
  rw [weightedDivergence_congr he, weightedDivergence_smul _ _ x hp
    (((liftScalar_contDiff hφ x hp).contDiffAt (isOpen_positiveCoordinates.mem_nhds hp)).differentiableAt (by simp))
    (((hVs x hp).contDiffAt (isOpen_positiveCoordinates.mem_nhds hp)).differentiableAt (by simp))]
  unfold localizedDivergence
  rw [hD x hp, directional_coordinateProjection φ hφ V hVd x hp]
  rfl

theorem integral_localizedDivergence (S : Space) (φ D : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (V : Coordinates → Coordinates)
    (hVs : ContDiffOn ℝ ∞ V positiveCoordinates) (hVd : IsDeckVectorField V)
    (hK : IsCompact (projectedVectorSupport V)) (hsφ : tsupport φ ⊆ (quotientChart S).source)
    (hD : ∀ x ∈ positiveCoordinates, D (coordinateProjection x) = weightedDivergence V x) :
    ∫ q, localizedDivergence φ D V q ∂orbitVolume = 0 := by
  let W := localizedVector S φ V
  have hW : ContDiff ℝ ∞ W := localizedVector_smooth S φ hφ V hVs hK hsφ
  have hcW : HasCompactSupport W := localizedVector_compact S φ V hK hsφ
  have hsW : tsupport W ⊆ (quotientChart S).target := localizedVector_tsupport_chart S φ V hK hsφ
  have ho (q : OrbitSpace) (hq : q ∉ (quotientChart S).source) : localizedDivergence φ D V q = 0 := by
    by_contra hn
    exact hq (hsφ (localizedDivergence_support φ D V hn))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (quotientChart S).source) ho,
    orbitVolume_integral_chart]
  calc
    _ = ∫ x in (quotientChart S).target, coordinateDensity x * weightedDivergence W x := by
      apply setIntegral_congr_fun (quotientChart S).open_target.measurableSet
      intro x hx
      dsimp only
      rw [quotientChart_projection_coordinates S hx, localizedDivergence_coordinate S φ D hφ V hVs hVd hD x hx]
    _ = ∫ x, coordinateDensity x * weightedDivergence W x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [weightedDivergence_zero_of_notMem_tsupport W x (fun h => hx (hsW h)), mul_zero])
    _ = 0 := integral_compact_weightedDivergence W hW hcW (hsW.trans (quotientChart_target_subset S))

end TernaryPoly.QuotientScalarDescent
