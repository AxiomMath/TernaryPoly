module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.ScalarDifferential
public import TernaryPeriodPolynomials.DifferentialForm.Connection.FiniteScalarEstimate

@[expose] public section

/-! Finite smooth gluing with control in the actual Riemannian dual metric. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set
open scoped ContDiff Manifold Bundle Topology
attribute [local instance] orbitMetricSpace
variable {ι : Type} [Fintype ι]

/-- A finite partition of smooth local products defines a globally smooth scalar. -/
theorem contMDiff_finite_scalar_gluing (φ g : ι → OrbitSpace → ℝ)
    (hφ : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (φ i))
    (hg : ∀ i y, y ∈ tsupport (φ i) → ContMDiffAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (g i) y) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (∑ i, φ i * g i) := by
  convert ContMDiff.sum (t := Finset.univ)
    (fun i _ => contMDiff_mul_of_smooth_near_support (φ i) (g i) (hφ i) (hg i)) using 1
  ext x
  simp only [Finset.sum_apply, Pi.mul_apply]

/-- Differentiating the partition near the nonzero support cancels its total covector. -/
theorem scalar_partition_derivative_cancel (φ : ι → OrbitSpace → ℝ) (f : OrbitSpace → ℝ)
    (hφ : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (φ i)) (hf : Continuous f)
    (hp : ∀ y, f y ≠ 0 → ∑ i, φ i y = 1) (x : OrbitSpace)
    (v : TangentSpace 𝓘(ℝ, Coordinates) x) :
    f x * (∑ i, scalarDifferential (φ i) x v) = 0 := by
  by_cases hx : f x = 0
  · simp [hx]
  have he : (∑ i, φ i) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hf.continuousAt.eventually_ne hx] with y hy
    simpa only [Finset.sum_apply] using hp y hy
  have hd := (scalarDifferential_congr he).trans (scalarDifferential_const 1 x)
  rw [scalarDifferential_sum φ x (fun i => (hφ i).mdifferentiable (by simp) x)] at hd
  have hz := congrArg (fun A : TangentSpace 𝓘(ℝ, Coordinates) x →L[ℝ] ℝ => A v) hd
  have hz' : ∑ i, scalarDifferential (φ i) x v = 0 := by simpa using hz
  rw [hz', mul_zero]

/-- The value bound needs only local accuracy wherever the partition weights are supported. -/
theorem finite_scalar_gluing_error (φ g : ι → OrbitSpace → ℝ) (f : OrbitSpace → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hn : ∀ i x, 0 ≤ φ i x) (hs : ∀ x, ∑ i, φ i x ≤ 1)
    (hp : ∀ x, f x ≠ 0 → ∑ i, φ i x = 1)
    (he : ∀ i x, x ∈ tsupport (φ i) → |g i x - f x| ≤ δ) (x : OrbitSpace) :
    |(∑ i, φ i * g i) x - f x| ≤ δ := by
  simp only [Finset.sum_apply, Pi.mul_apply]
  apply PolynomialFormConnection.abs_partition_error_le (fun i => φ i x) (fun i => g i x) (f x)
    hδ (fun i => hn i x) (hs x)
  · by_cases hx : f x = 0
    · simp [hx]
    · rw [hp x hx, one_mul]
  · intro i hi
    exact he i x (subset_closure hi)

/-- The actual covector error is bounded by the main slope plus a finite partition-error term. -/
theorem finite_scalar_gluing_differential_bound (φ g : ι → OrbitSpace → ℝ) (f : OrbitSpace → ℝ)
    (hφ : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (φ i))
    (hg : ∀ i y, y ∈ tsupport (φ i) → ContMDiffAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (g i) y)
    (hf : Continuous f) {L δ D : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hD : 0 ≤ D)
    (hn : ∀ i x, 0 ≤ φ i x) (hs : ∀ x, ∑ i, φ i x ≤ 1)
    (hp : ∀ x, f x ≠ 0 → ∑ i, φ i x = 1)
    (he : ∀ i x, x ∈ tsupport (φ i) → |g i x - f x| ≤ δ)
    (hgd : ∀ i x, x ∈ tsupport (φ i) → ‖scalarDifferential (g i) x‖ ≤ L)
    (hφd : ∀ i x, ‖scalarDifferential (φ i) x‖ ≤ D) (x : OrbitSpace) :
    ‖scalarDifferential (∑ i, φ i * g i) x‖ ≤ L + (Fintype.card ι : ℝ) * δ * D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hprod i := contMDiff_mul_of_smooth_near_support (φ i) (g i) (hφ i) (hg i)
  rw [scalarDifferential_sum (fun i => φ i * g i) x
    (fun i => (hprod i).mdifferentiable (by simp) x)]
  simp only [_root_.sum_apply]
  simp_rw [scalarDifferential_mul_of_smooth_near_support _ _ x (hφ _) (hg _),
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [Real.norm_eq_abs]
  apply PolynomialFormConnection.abs_partition_derivative_le
    (fun i => φ i x) (fun i => g i x) (fun i => scalarDifferential (g i) x v)
    (fun i => scalarDifferential (φ i) x v) (f x) hL hδ hD (norm_nonneg v)
    (fun i => hn i x) (hs x)
  · intro i hi
    have hb := (scalarDifferential (g i) x).le_opNorm v
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hgd i x (subset_closure hi)) (norm_nonneg v))
  · intro i
    have hb := (scalarDifferential (φ i) x).le_opNorm v
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hφd i x) (norm_nonneg v))
  · intro i hi
    apply he i x
    by_contra hnots
    rw [scalarDifferential_eq_zero_of_notMem_tsupport hnots, _root_.zero_apply] at hi
    exact hi rfl
  · exact scalar_partition_derivative_cancel φ f hφ hf hp x v

end TernaryPoly.SymmetricSpaceRiemannian
