module

public import TernaryPeriodPolynomials.DifferentialForm.FiniteScalarPartition
public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCutoff

@[expose] public section


/-! Compact quotient scalars transported through their actual quotient chart. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
  SymmetricSpaceQuotientManifold
open scoped ContDiff Manifold Topology

/-- Pull back on the target of the actual chart, and extend by zero. -/
def coordinateScalar (S : Space) (ψ : OrbitSpace → ℝ) : Coordinates → ℝ :=
  (quotientChart S).target.indicator (ψ ∘ (quotientChart S).symm)

theorem coordinateScalar_apply (S : Space) (ψ : OrbitSpace → ℝ) {x : Coordinates}
    (hx : x ∈ (quotientChart S).target) :
    coordinateScalar S ψ x = ψ ((quotientChart S).symm x) := indicator_of_mem hx _

theorem tsupport_coordinateScalar (S : Space) (ψ : OrbitSpace → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (quotientChart S).source) :
    tsupport (coordinateScalar S ψ) ⊆ (quotientChart S) '' tsupport ψ := by
  have hK := hc.image_of_continuousOn ((quotientChart S).continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hxt : x ∈ (quotientChart S).target := by
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  have hn : ψ ((quotientChart S).symm x) ≠ 0 := by
    change coordinateScalar S ψ x ≠ 0 at hx
    rwa [coordinateScalar_apply S ψ hxt] at hx
  exact ⟨(quotientChart S).symm x, subset_closure hn, (quotientChart S).right_inv hxt⟩

theorem coordinateScalar_properties (S : Space) (ψ : OrbitSpace → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (quotientChart S).source) :
    ContDiff ℝ ∞ (coordinateScalar S ψ) ∧ HasCompactSupport (coordinateScalar S ψ) ∧
      tsupport (coordinateScalar S ψ) ⊆ (quotientChart S).target := by
  have hK := hc.image_of_continuousOn ((quotientChart S).continuousOn.mono hs)
  have ht : tsupport (coordinateScalar S ψ) ⊆ (quotientChart S).target := by
    rintro x hx
    obtain ⟨q, hq, rfl⟩ := tsupport_coordinateScalar S ψ hc hs hx
    exact (quotientChart S).map_source (hs hq)
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure (tsupport_coordinateScalar S ψ hc hs), ht⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport (coordinateScalar S ψ)
  · have hx' := ht hx
    have hf : ContDiffOn ℝ ∞ (ψ ∘ (quotientChart S).symm) (quotientChart S).target :=
      contMDiffOn_iff_contDiffOn.mp (hψ.comp_contMDiffOn (quotientChart_symm_contMDiffOn S))
    apply (hf.contDiffAt ((quotientChart S).open_target.mem_nhds hx')).congr_of_eventuallyEq
    filter_upwards [(quotientChart S).open_target.mem_nhds hx'] with y hy
    exact coordinateScalar_apply S ψ hy
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

theorem exists_coordinateScalar_outer_cutoff (S : Space) (ψ : OrbitSpace → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (quotientChart S).source) :
    ∃ η : Coordinates → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ (quotientChart S).target ∧ η * coordinateScalar S ψ = coordinateScalar S ψ := by
  obtain ⟨_, hχc, hχs⟩ := coordinateScalar_properties S ψ hψ hc hs
  obtain ⟨η, hη, hηc, hηs, hη1⟩ := CompactSmoothCutoff.exists_cutoff hχc
    (quotientChart S).open_target hχs
  refine ⟨η, hη, hηc, hηs, ?_⟩
  funext x
  by_cases hx : x ∈ tsupport (coordinateScalar S ψ)
  · change η x * coordinateScalar S ψ x = _
    rw [(hη1 x hx).eq_of_nhds, Pi.one_apply, one_mul]
  · change η x * coordinateScalar S ψ x = _
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

end TernaryPoly.PolynomialFormCoordinates
