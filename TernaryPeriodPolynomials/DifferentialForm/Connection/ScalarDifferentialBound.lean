module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.ScalarDifferential

@[expose] public section


/-! Compactly supported smooth partition scalars have a bound in the actual dual metric. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set
open scoped ContDiff Manifold Bundle Topology
attribute [local instance] orbitMetricSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

/-- A compact scalar supported in a normalized chart has globally bounded actual covector norm. -/
theorem exists_scalarDifferential_bound (q : OrbitSpace) (φ : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ φ) (hK : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (normalizedChart q).source)
    (hb : ∀ y ∈ tsupport φ, ‖normalizedChartDerivative q y‖ ≤ 2) :
    ∃ D > 0, ∀ y, ‖scalarDifferential φ y‖ ≤ D := by
  let g : TangentSpace 𝓘(ℝ, Coordinates) q → ℝ := φ ∘ (normalizedChart q).symm
  have hg : ContDiffOn ℝ ∞ g (normalizedChart q).target := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hφ.comp_contMDiffOn (contMDiffOn_normalizedChart_symm q)
  have hc : IsCompact (normalizedChart q '' tsupport φ) :=
    hK.image_of_continuousOn ((normalizedChart q).continuousOn.mono hs)
  have ht : normalizedChart q '' tsupport φ ⊆ (normalizedChart q).target := by
    rintro v ⟨y, hy, rfl⟩
    exact (normalizedChart q).map_source (hs hy)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen (normalizedChart q).open_target (by simp)).mono ht)
  refine ⟨2 * (|C| + 1), by positivity, fun y => ?_⟩
  by_cases hy : y ∈ tsupport φ
  · have hys := hs hy
    have hyt := (normalizedChart q).map_source hys
    have he : φ =ᶠ[𝓝 y] g ∘ normalizedChart q := by
      filter_upwards [(normalizedChart q).open_source.mem_nhds hys] with z hz
      exact congrArg φ ((normalizedChart q).left_inv hz).symm
    have hdg : DifferentiableAt ℝ g (normalizedChart q y) :=
      ((hg.differentiableOn (by simp)) _ hyt).differentiableAt
        ((normalizedChart q).open_target.mem_nhds hyt)
    rw [scalarDifferential_congr he, scalarDifferential_comp_normalizedChart q y g hdg hys]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hCg : ‖fderiv ℝ g (normalizedChart q y)‖ ≤ |C| + 1 :=
      (hC _ (mem_image_of_mem _ hy)).trans (by linarith [le_abs_self C])
    have hbound := mul_le_mul hCg (hb y hy) (ContinuousLinearMap.opNorm_nonneg _) (by positivity : 0 ≤ |C| + 1)
    nlinarith
  · rw [scalarDifferential_eq_zero_of_notMem_tsupport hy]
    simp only [ContinuousLinearMap.opNorm_zero]
    positivity

end TernaryPoly.SymmetricSpaceRiemannian
