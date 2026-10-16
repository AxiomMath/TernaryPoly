module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.DirectionalScalar
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section


/-! Compact coordinate representatives of chart-localized actual quotient vector fields. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  SmoothCoveringDeRham SmoothDeRhamGluing PolynomialFormConnection Set Filter
open scoped ContDiff Manifold Topology

def projectedVectorSupport (V : Coordinates → Coordinates) : Set OrbitSpace :=
  closure (coordinateProjection '' Function.support V)

def localizedVector (S : Space) (φ : OrbitSpace → ℝ) (V : Coordinates → Coordinates)
    (x : Coordinates) : Coordinates := by
  classical
  exact if x ∈ (quotientChart S).target then liftScalar φ x • V x else 0

theorem localizedVector_apply (S : Space) (φ : OrbitSpace → ℝ) (V : Coordinates → Coordinates)
    (x : Coordinates) (hx : x ∈ (quotientChart S).target) :
    localizedVector S φ V x = liftScalar φ x • V x := by simp only [localizedVector, ite_eq_left hx]

theorem compact_chart_support (S : Space) (φ : OrbitSpace → ℝ) (K : Set OrbitSpace)
    (hK : IsCompact K) (hsφ : tsupport φ ⊆ (quotientChart S).source) :
    IsCompact ((quotientChart S) '' (K ∩ tsupport φ)) :=
  (hK.inter_right (isClosed_tsupport φ)).image_of_continuousOn
    ((quotientChart S).continuousOn.mono (fun _ h => hsφ h.2))

theorem localizedVector_tsupport_subset (S : Space) (φ : OrbitSpace → ℝ)
    (V : Coordinates → Coordinates) (hK : IsCompact (projectedVectorSupport V))
    (hsφ : tsupport φ ⊆ (quotientChart S).source) :
    tsupport (localizedVector S φ V) ⊆
      (quotientChart S) '' (projectedVectorSupport V ∩ tsupport φ) := by
  apply closure_minimal _ (compact_chart_support S φ _ hK hsφ).isClosed
  intro x hx
  have ht : x ∈ (quotientChart S).target := by
    by_contra ht
    exact hx (by simp only [localizedVector, ite_eq_right ht])
  have hv : V x ≠ 0 := by
    intro hz
    apply hx
    rw [localizedVector_apply S φ V x ht, hz, smul_zero]
  have hp : φ (coordinateProjection x) ≠ 0 := by
    intro hz
    apply hx
    rw [localizedVector_apply S φ V x ht]
    change φ (coordinateProjection x) • V x = 0
    rw [hz, zero_smul]
  refine ⟨coordinateProjection x, ⟨subset_closure (mem_image_of_mem _ hv), subset_tsupport _ hp⟩, ?_⟩
  rw [← quotientChart_projection_coordinates S ht]
  exact (quotientChart S).right_inv ht

theorem localizedVector_tsupport_chart (S : Space) (φ : OrbitSpace → ℝ)
    (V : Coordinates → Coordinates) (hK : IsCompact (projectedVectorSupport V))
    (hsφ : tsupport φ ⊆ (quotientChart S).source) :
    tsupport (localizedVector S φ V) ⊆ (quotientChart S).target := by
  intro x hx
  obtain ⟨q,hq,rfl⟩ := localizedVector_tsupport_subset S φ V hK hsφ hx
  exact (quotientChart S).map_source (hsφ hq.2)

theorem localizedVector_compact (S : Space) (φ : OrbitSpace → ℝ)
    (V : Coordinates → Coordinates) (hK : IsCompact (projectedVectorSupport V))
    (hsφ : tsupport φ ⊆ (quotientChart S).source) :
    HasCompactSupport (localizedVector S φ V) :=
  (compact_chart_support S φ _ hK hsφ).of_isClosed_subset (isClosed_tsupport _)
    (localizedVector_tsupport_subset S φ V hK hsφ)

theorem localizedVector_smooth (S : Space) (φ : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (V : Coordinates → Coordinates)
    (hVs : ContDiffOn ℝ ∞ V positiveCoordinates) (hK : IsCompact (projectedVectorSupport V))
    (hsφ : tsupport φ ⊆ (quotientChart S).source) : ContDiff ℝ ∞ (localizedVector S φ V) := by
  apply CompactCoordinateIntegration.contDiff_of_tsupport_subset (quotientChart S).open_target
  · apply (((liftScalar_contDiff hφ).smul hVs).mono (quotientChart_target_subset S)).congr
    intro x hx
    exact localizedVector_apply S φ V x hx
  · exact localizedVector_tsupport_chart S φ V hK hsφ

end TernaryPoly.QuotientScalarDescent
