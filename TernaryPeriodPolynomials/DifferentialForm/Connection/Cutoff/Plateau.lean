module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.GlobalSmooth
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-! A fixed smooth plateau turns quantitative approximation into exact compact cutoffs. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set Metric
open scoped ContDiff Manifold Bundle Topology
attribute [local instance] orbitMetricSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

/-- A single fixed scalar plateau, equal to one near one and zero near zero. -/
def cutoffPlateau : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem cutoffPlateau_one {t : ℝ} (ht : dist t 1 ≤ 1 / 8) : cutoffPlateau t = 1 := by
  apply cutoffPlateau.one_of_mem_closedBall
  change dist t 1 ≤ (1 : ℝ) / 4
  linarith

theorem cutoffPlateau_zero {t : ℝ} (ht : dist t 0 ≤ 1 / 8) : cutoffPlateau t = 0 := by
  apply cutoffPlateau.zero_of_le_dist
  change (1 : ℝ) / 2 ≤ dist t 1
  have htri := dist_triangle (1 : ℝ) t 0
  rw [dist_comm 1 t] at htri
  norm_num at htri
  have ht' : |t| ≤ 1 / 8 := by simpa only [Real.dist_eq, sub_zero] using ht
  linarith

/-- Compact support of its derivative gives one fixed global slope bound. -/
theorem exists_cutoffPlateau_derivative_bound :
    ∃ A > 0, ∀ t : ℝ, ‖fderiv ℝ cutoffPlateau t‖ ≤ A := by
  have hβ : ContDiff ℝ ∞ (cutoffPlateau : ℝ → ℝ) := cutoffPlateau.contDiff
  obtain ⟨A, hA⟩ := (cutoffPlateau.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hβ.continuous_fderiv (by simp))
  refine ⟨|A| + 1, by positivity, fun t => ?_⟩
  exact (hA t).trans (by linarith [le_abs_self A])

theorem scalarDifferential_comp_scalar (b : ℝ → ℝ) (g : OrbitSpace → ℝ) (q : OrbitSpace)
    (hb : DifferentiableAt ℝ b (g q))
    (hg : MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) g q) :
    scalarDifferential (b ∘ g) q = fderiv ℝ b (g q) ∘L scalarDifferential g q := by
  change mfderiv _ _ (b ∘ g) q = _
  rw [mfderiv_comp q hb.mdifferentiableAt hg, mfderiv_eq_fderiv]
  rfl

/-- A close approximation to a compactly supported scalar gives a compact exact cutoff. -/
theorem cutoffPlateau_comp_properties (f g : OrbitSpace → ℝ)
    (hf : HasCompactSupport f) (hg : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ g)
    (he : ∀ q, dist (g q) (f q) ≤ 1 / 8) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (cutoffPlateau ∘ g) ∧
      HasCompactSupport (cutoffPlateau ∘ g) ∧
      (∀ q, (cutoffPlateau ∘ g) q ∈ Icc (0 : ℝ) 1) ∧
      ∀ q, f q = 1 → (cutoffPlateau ∘ g) q = 1 := by
  refine ⟨cutoffPlateau.contDiff.contMDiff.comp hg, ?_, fun q => ⟨cutoffPlateau.nonneg, cutoffPlateau.le_one⟩, ?_⟩
  · apply HasCompactSupport.intro (K := tsupport f) hf
    intro q hq
    have hfq : f q = 0 := (notMem_tsupport_iff_eventuallyEq.mp hq).eq_of_nhds
    apply cutoffPlateau_zero
    simpa only [hfq] using he q
  · intro q hq
    apply cutoffPlateau_one
    simpa only [hq] using he q

/-- The chain rule keeps the final cutoff bound in the actual dual-Riemannian norm. -/
theorem norm_scalarDifferential_cutoffPlateau_le (g : OrbitSpace → ℝ)
    (hg : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ g) {A B : ℝ}
    (hA : 0 ≤ A) (hAb : ∀ t : ℝ, ‖fderiv ℝ cutoffPlateau t‖ ≤ A)
    (hB : ∀ q, ‖scalarDifferential g q‖ ≤ B) (q : OrbitSpace) :
    ‖scalarDifferential (cutoffPlateau ∘ g) q‖ ≤ A * B := by
  have hβ : ContDiff ℝ ∞ (cutoffPlateau : ℝ → ℝ) := cutoffPlateau.contDiff
  rw [scalarDifferential_comp_scalar cutoffPlateau g q
    (hβ.differentiable (by simp) _) (hg.mdifferentiable (by simp) q)]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hAb _) (hB q) (ContinuousLinearMap.opNorm_nonneg _) hA)

end TernaryPoly.SymmetricSpaceRiemannian
