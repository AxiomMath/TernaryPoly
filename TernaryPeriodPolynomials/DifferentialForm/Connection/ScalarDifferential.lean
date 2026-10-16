module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.LocalSmooth
public import Mathlib.Geometry.Manifold.Algebra.Structures

@[expose] public section


/-! Calculus for the actual quotient scalar covector used in bounded-gradient gluing. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set
open scoped ContDiff Manifold Bundle Topology
attribute [local instance] orbitMetricSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

@[simp] theorem scalarDifferential_const (c : ℝ) (q : OrbitSpace) :
    scalarDifferential (fun _ => c) q = 0 := mfderiv_const

theorem scalarDifferential_congr {f g : OrbitSpace → ℝ} {q : OrbitSpace}
    (h : f =ᶠ[𝓝 q] g) : scalarDifferential f q = scalarDifferential g q := h.mfderiv_eq

theorem scalarDifferential_eq_zero_of_notMem_tsupport {f : OrbitSpace → ℝ} {q : OrbitSpace}
    (h : q ∉ tsupport f) : scalarDifferential f q = 0 := by
  have he : f =ᶠ[𝓝 q] 0 := (notMem_tsupport_iff_eventuallyEq.mp h)
  exact (scalarDifferential_congr he).trans (scalarDifferential_const 0 q)

theorem scalarDifferential_mul {f g : OrbitSpace → ℝ} {q : OrbitSpace}
    (hf : MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) f q)
    (hg : MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) g q) :
    scalarDifferential (f * g) q = f q • scalarDifferential g q + g q • scalarDifferential f q :=
  (hf.hasMFDerivAt.mul hg.hasMFDerivAt).mfderiv

theorem scalarDifferential_sum {ι : Type} [Fintype ι] (f : ι → OrbitSpace → ℝ) (q : OrbitSpace)
    (hf : ∀ i, MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) (f i) q) :
    scalarDifferential (∑ i, f i) q = ∑ i, scalarDifferential (f i) q :=
  (HasMFDerivAt.sum (t := Finset.univ) (f := f) (f' := fun i => scalarDifferential (f i) q)
    (fun i _ => (hf i).hasMFDerivAt)).mfderiv

/-- A smooth cutoff removes any regularity requirement outside its support. -/
theorem scalarDifferential_mul_of_smooth_near_support (φ g : OrbitSpace → ℝ) (q : OrbitSpace)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ φ)
    (hg : ∀ y ∈ tsupport φ, ContMDiffAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ g y) :
    scalarDifferential (φ * g) q = φ q • scalarDifferential g q + g q • scalarDifferential φ q := by
  by_cases hq : q ∈ tsupport φ
  · exact scalarDifferential_mul (hφ.mdifferentiable (by simp) q)
      ((hg q hq).mdifferentiableAt (by simp))
  · have he : φ =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    have hz : φ q = 0 := he.eq_of_nhds
    have hp : φ * g =ᶠ[𝓝 q] 0 := by
      filter_upwards [he] with y hy
      simp only [Pi.mul_apply, hy, zero_mul, Pi.zero_apply]
    rw [scalarDifferential_congr hp, show scalarDifferential (0 : OrbitSpace → ℝ) q = 0 from scalarDifferential_const 0 q, hz,
      scalarDifferential_eq_zero_of_notMem_tsupport hq, zero_smul, smul_zero, add_zero]

/-- The same support condition gives genuine global smoothness of the product. -/
theorem contMDiff_mul_of_smooth_near_support (φ g : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ φ)
    (hg : ∀ y ∈ tsupport φ, ContMDiffAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ g y) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (φ * g) := by
  intro q
  by_cases hq : q ∈ tsupport φ
  · exact (hφ q).mul (hg q hq)
  · have he : φ =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp only [Pi.mul_apply, hy, zero_mul, Pi.zero_apply]

end TernaryPoly.SymmetricSpaceRiemannian
