module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.NormalizedRadius
public import TernaryPeriodPolynomials.DifferentialForm.Connection.LipschitzConvolution

@[expose] public section


/-! Actual quantitative scalar smoothing in normalized quotient charts. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set Metric MeasureTheory
open scoped ContDiff Manifold Bundle Topology NNReal
attribute [local instance] orbitMetricSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

/-- A global metric-Lipschitz quotient scalar has arbitrarily close smooth local approximations,
with uniform coordinate Lipschitz constant at most twice the original one. -/
theorem exists_normalized_smooth_approx (q : OrbitSpace) (r : ℝ)
    (h : ∀ v ∈ ball (normalizedChart q q) r,
      v ∈ (normalizedChart q).target ∧ ‖normalizedChartInverseDerivative q v‖ < 2)
    {f : OrbitSpace → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : TangentSpace 𝓘(ℝ, Coordinates) q → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith (K * 2) g ∧
      ∀ v ∈ ball (normalizedChart q q) r, dist (g v) (f ((normalizedChart q).symm v)) < ε := by
  let T := TangentSpace 𝓘(ℝ, Coordinates) q
  let : FiniteDimensional ℝ T :=
    FiniteDimensional.of_injective (tangentCoordinates q).toLinearMap (tangentCoordinates q).injective
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  have hloc := hf.comp_lipschitzOnWith (normalizedChart_symm_lipschitz q r h)
  obtain ⟨F, hF, he⟩ := hloc.extend_real
  obtain ⟨g, hg, hgl, hge, _⟩ := PolynomialFormConnection.exists_smooth_lipschitz_approx
    (Measure.addHaar (G := T)) hF hε
  refine ⟨g, hg, hgl, ?_⟩
  intro v hv
  change dist (g v) ((f ∘ (normalizedChart q).symm) v) < ε
  rw [he hv]
  exact hge v

/-- The genuine scalar differential, interpreted as a covector in the actual tangent norm. -/
def scalarDifferential (f : OrbitSpace → ℝ) (q : OrbitSpace) :
    TangentSpace 𝓘(ℝ, Coordinates) q →L[ℝ] ℝ :=
  mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) f q

/-- The normalized-coordinate chain rule has its literal scalar differential as output. -/
theorem scalarDifferential_comp_normalizedChart (q y : OrbitSpace)
    (g : TangentSpace 𝓘(ℝ, Coordinates) q → ℝ) (hg : DifferentiableAt ℝ g (normalizedChart q y))
    (hy : y ∈ (normalizedChart q).source) :
    scalarDifferential (g ∘ normalizedChart q) y =
      (fderiv ℝ g (normalizedChart q y)) ∘L normalizedChartDerivative q y := by
  have hc : MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q)
      (normalizedChart q) y :=
    ((contMDiffOn_normalizedChart q).contMDiffAt ((normalizedChart q).open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  change mfderiv _ _ (g ∘ normalizedChart q) y = _
  rw [mfderiv_comp y hg.mdifferentiableAt hc, mfderiv_eq_fderiv]
  rfl

/-- Coordinate smoothing controls the actual Riemannian dual norm by four times the input slope. -/
theorem norm_scalarDifferential_comp_normalizedChart_le (q y : OrbitSpace)
    {g : TangentSpace 𝓘(ℝ, Coordinates) q → ℝ} {K : ℝ≥0}
    (hg : ContDiff ℝ ∞ g) (hgl : LipschitzWith (K * 2) g)
    (hy : y ∈ (normalizedChart q).source) (hb : ‖normalizedChartDerivative q y‖ ≤ 2) :
    ‖scalarDifferential (g ∘ normalizedChart q) y‖ ≤ 4 * (K : ℝ) := by
  rw [scalarDifferential_comp_normalizedChart q y g (hg.differentiable (by simp) _) hy]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hf := norm_fderiv_le_of_lipschitz ℝ hgl (x₀ := normalizedChart q y)
  calc
    _ ≤ ((K : ℝ) * 2) * 2 := mul_le_mul hf hb (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    _ = _ := by ring

end TernaryPoly.SymmetricSpaceRiemannian
