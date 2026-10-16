module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.RiemannianProper
public import TernaryPeriodPolynomials.DifferentialForm.Connection.RiemannianLipschitz

@[expose] public section


/-! Normalized quotient coordinates measured in the genuine tangent norm at their center. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open Manifold Bundle Filter Set
open scoped ContDiff Manifold Bundle Topology
attribute [local instance] orbitMetricSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

/-- The preferred chart identifies the genuine tangent fiber with the fixed coordinate model. -/
def tangentCoordinates (q : OrbitSpace) : TangentSpace 𝓘(ℝ, Coordinates) q ≃L[ℝ] Coordinates :=
  (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).continuousLinearEquivAt ℝ q
    (FiberBundle.mem_baseSet_trivializationAt' q)

/-- Read a chart in the actual Riemannian norm at its center. -/
def normalizedChart (q : OrbitSpace) :
    OpenPartialHomeomorph OrbitSpace (TangentSpace 𝓘(ℝ, Coordinates) q) :=
  (chartAt Coordinates q).trans (tangentCoordinates q).symm.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem normalizedChart_source (q : OrbitSpace) :
    (normalizedChart q).source = (chartAt Coordinates q).source := by
  simp [normalizedChart]

@[simp] theorem normalizedChart_apply (q y : OrbitSpace) :
    normalizedChart q y = (tangentCoordinates q).symm (chartAt Coordinates q y) := rfl

@[simp] theorem normalizedChart_symm_apply (q : OrbitSpace)
    (v : TangentSpace 𝓘(ℝ, Coordinates) q) :
    (normalizedChart q).symm v = (chartAt Coordinates q).symm (tangentCoordinates q v) := rfl

/-- The chart normalized at its center has norm distortion less than two nearby. -/
theorem eventually_norm_normalized_chart_trivialization_lt (q : OrbitSpace) :
    ∀ᶠ y in 𝓝 q, ‖(tangentCoordinates q).symm.toContinuousLinearMap ∘L
      (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).continuousLinearMapAt ℝ y‖ < 2 := by
  have h := eventually_norm_symmL_trivializationAt_self_comp_lt Coordinates
    (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) q one_lt_two
  simpa only [tangentCoordinates, Trivialization.symm_continuousLinearEquivAt_eq'] using h

/-- The normalized coordinates are smooth on the actual chart source. -/
theorem contMDiffOn_normalizedChart (q : OrbitSpace) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) ∞
      (normalizedChart q) (normalizedChart q).source := by
  rw [normalizedChart_source]
  exact (tangentCoordinates q).symm.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

/-- The inverse normalized coordinates are smooth on their target. -/
theorem contMDiffOn_normalizedChart_symm (q : OrbitSpace) :
    ContMDiffOn 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) 𝓘(ℝ, Coordinates) ∞
      (normalizedChart q).symm (normalizedChart q).target := by
  have hc : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) ∞
      (chartAt Coordinates q).symm (chartAt Coordinates q).target := contMDiffOn_chart_symm
  have hG : ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) 𝓘(ℝ, Coordinates) ∞
      (tangentCoordinates q) := (tangentCoordinates q).contDiff.contMDiff
  change ContMDiffOn _ _ ∞ ((chartAt Coordinates q).symm ∘ tangentCoordinates q) _
  apply hc.comp hG.contMDiffOn
  intro v hv
  exact hv.2

/-- Its literal manifold derivative is the normalized tangent trivialization. -/
theorem mfderiv_normalizedChart (q y : OrbitSpace) (hy : y ∈ (normalizedChart q).source) :
    mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) (normalizedChart q) y =
      (tangentCoordinates q).symm.toContinuousLinearMap ∘L
        (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).continuousLinearMapAt ℝ y := by
  rw [normalizedChart_source] at hy
  have hc : MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (chartAt Coordinates q) y :=
    (mdifferentiable_chart q).mdifferentiableAt hy
  change mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q)
    ((tangentCoordinates q).symm ∘ chartAt Coordinates q) y = _
  have hdG : MDifferentiable 𝓘(ℝ, Coordinates) 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q)
      (tangentCoordinates q).symm := (tangentCoordinates q).symm.differentiable.mdifferentiable
  rw [mfderiv_comp y (hdG _) hc]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy]
  simp only [mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  congr 1


/-- The inverse derivative is the oppositely normalized tangent trivialization. -/
theorem mfderiv_normalizedChart_symm (q : OrbitSpace)
    (v : TangentSpace 𝓘(ℝ, Coordinates) q) (hv : v ∈ (normalizedChart q).target) :
    mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) 𝓘(ℝ, Coordinates)
      (normalizedChart q).symm v =
      (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).symmL ℝ
        ((normalizedChart q).symm v) ∘L (tangentCoordinates q).toContinuousLinearMap := by
  have hgv : tangentCoordinates q v ∈ (chartAt Coordinates q).target := hv.2
  have hy : (normalizedChart q).symm v ∈ (chartAt Coordinates q).source :=
    (chartAt Coordinates q).map_target hgv
  have he : extChartAt 𝓘(ℝ, Coordinates) q ((normalizedChart q).symm v) =
      tangentCoordinates q v := (chartAt Coordinates q).right_inv hgv
  have hc : MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates)
      (chartAt Coordinates q).symm (tangentCoordinates q v) :=
    (mdifferentiable_chart q).symm.mdifferentiableAt hgv
  have hG : MDifferentiable 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) 𝓘(ℝ, Coordinates)
      (tangentCoordinates q) := (tangentCoordinates q).differentiable.mdifferentiable
  change mfderiv _ _ ((chartAt Coordinates q).symm ∘ tangentCoordinates q) v = _
  rw [mfderiv_comp v hc (hG _), TangentBundle.symmL_trivializationAt hy]
  simp only [mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  congr 1
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ]
  congr 1
  exact he.symm

/-- The normalized differential, with its actual source and target normed spaces explicit. -/
def normalizedChartDerivative (q y : OrbitSpace) :
    TangentSpace 𝓘(ℝ, Coordinates) y →L[ℝ] TangentSpace 𝓘(ℝ, Coordinates) q :=
  mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) (normalizedChart q) y

/-- The inverse differential, with its actual source and target normed spaces explicit. -/
def normalizedChartInverseDerivative (q : OrbitSpace) (v : TangentSpace 𝓘(ℝ, Coordinates) q) :
    TangentSpace 𝓘(ℝ, Coordinates) q →L[ℝ]
      TangentSpace 𝓘(ℝ, Coordinates) ((normalizedChart q).symm v) :=
  mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, Coordinates) q) 𝓘(ℝ, Coordinates) (normalizedChart q).symm v

/-- The normalized chart derivative has norm less than two near its center. -/
theorem eventually_norm_normalizedChartDerivative_lt (q : OrbitSpace) :
    ∀ᶠ y in 𝓝 q, y ∈ (normalizedChart q).source ∧ ‖normalizedChartDerivative q y‖ < 2 := by
  filter_upwards [eventually_norm_normalized_chart_trivialization_lt q,
    (normalizedChart q).open_source.mem_nhds (by rw [normalizedChart_source]; exact mem_chart_source Coordinates q)]
    with y hf hy
  refine ⟨hy, ?_⟩
  rw [normalizedChartDerivative, mfderiv_normalizedChart q y hy]
  exact hf

/-- Both derivative directions have norm less than two on a coordinate neighborhood. -/
theorem eventually_normalizedChart_bounds (q : OrbitSpace) :
    ∀ᶠ v in 𝓝 (normalizedChart q q), v ∈ (normalizedChart q).target ∧
      ‖normalizedChartDerivative q ((normalizedChart q).symm v)‖ < 2 ∧
      ‖normalizedChartInverseDerivative q v‖ < 2 := by
  have hq : q ∈ (normalizedChart q).source := by
    rw [normalizedChart_source]
    exact mem_chart_source Coordinates q
  have hqi := (normalizedChart q).map_source hq
  have hinv : ContinuousAt (normalizedChart q).symm (normalizedChart q q) :=
    (normalizedChart q).symm.continuousAt hqi
  have hinv' : Tendsto (normalizedChart q).symm (𝓝 (normalizedChart q q)) (𝓝 q) := by
    change Tendsto (normalizedChart q).symm (𝓝 (normalizedChart q q))
      (𝓝 ((normalizedChart q).symm (normalizedChart q q))) at hinv
    rwa [(normalizedChart q).left_inv hq] at hinv
  have hback := eventually_norm_symmL_trivializationAt_comp_self_lt Coordinates
    (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) q one_lt_two
  have hG : (tangentCoordinates q).toContinuousLinearMap =
      (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).continuousLinearMapAt ℝ q :=
    Trivialization.coe_continuousLinearEquivAt_eq' _ _
  filter_upwards [hinv'.eventually (eventually_norm_normalizedChartDerivative_lt q),
    hinv'.eventually hback, (normalizedChart q).open_target.mem_nhds hqi] with v hf hb hv
  refine ⟨hv, hf.2, ?_⟩
  rw [normalizedChartInverseDerivative, mfderiv_normalizedChart_symm q v hv, hG]
  exact hb

end TernaryPoly.SymmetricSpaceRiemannian
