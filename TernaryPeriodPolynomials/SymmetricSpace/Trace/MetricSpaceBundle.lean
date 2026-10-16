module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricContinuousBilinear
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldProjection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

@[expose] public section


/-! The smooth trace metric on the genuine covering space of positive forms. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle ContinuousLinearMap
open scoped ContDiff Manifold Matrix.Norms.Elementwise

/-- The actual tangent pairing in the singleton coordinate atlas of positive forms. -/
def spaceInner (S : Space) :
    TangentSpace 𝓘(ℝ, Coordinates) S →L[ℝ] TangentSpace 𝓘(ℝ, Coordinates) S →L[ℝ] ℝ :=
  coordinateContinuousBilin (coordinateChart S)

@[simp] theorem spaceInner_apply (S : Space) (v w : TangentSpace 𝓘(ℝ, Coordinates) S) :
    spaceInner S v w = coordinatePair (coordinateChart S) v w := rfl

/-- The singleton atlas has identity tangent changes. -/
theorem space_tangent_symmL (S T : Space) :
    (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) S).symmL ℝ T =
      ContinuousLinearMap.id ℝ Coordinates := by
  have hT : T ∈ (chartAt Coordinates S).source := by rw [space_chartAt, coordinateChart_source]; trivial
  rw [TangentBundle.symmL_trivializationAt_eq_core hT]
  change (tangentBundleCore 𝓘(ℝ, Coordinates) Space).coordChange
    (achart Coordinates S) (achart Coordinates S) T = _
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentBundleCore 𝓘(ℝ, Coordinates) Space).coordChange_self (achart Coordinates S) T hT v

theorem spaceInner_inCoordinates (S T : Space) :
    inCoordinates Coordinates (TangentSpace 𝓘(ℝ, Coordinates) : Space → Type)
      (Coordinates →L[ℝ] ℝ) (fun T : Space => TangentSpace 𝓘(ℝ, Coordinates) T →L[ℝ] ℝ)
      S T S T (spaceInner T) = coordinateContinuousBilin (coordinateChart T) := by
  have hT : T ∈ (trivializationAt Coordinates
      (TangentSpace 𝓘(ℝ, Coordinates) : Space → Type) S).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, space_chartAt, coordinateChart_source]; trivial
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [inCoordinates_apply_eq₂ hT hT (by simp)]
  rw [← (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) S).symmL_apply (R := ℝ) hT v,
    ← (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) S).symmL_apply (R := ℝ) hT w,
    space_tangent_symmL]
  simp [spaceInner_apply]
  rfl

/-- The actual covering-space metric is a smooth bilinear section. -/
theorem contMDiff_spaceInner :
    ContMDiff 𝓘(ℝ, Coordinates)
      (𝓘(ℝ, Coordinates).prod 𝓘(ℝ, Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ)) ∞
      (fun S : Space => TotalSpace.mk' (Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) S
        (spaceInner S)) := by
  have hc : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) ∞
      (fun S : Space => coordinateContinuousBilin (coordinateChart S)) := by
    rw [← contMDiffOn_univ]
    exact contDiffOn_coordinateContinuousBilin.contMDiffOn.comp
      coordinateChart_contMDiff.contMDiffOn (fun S _ => extract_mem S)
  intro S
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply, spaceInner_inCoordinates]
  exact hc S

/-- The smooth positive metric on the literal five-dimensional covering manifold. -/
def spaceContMDiffRiemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, Coordinates) ∞ Coordinates
      (TangentSpace 𝓘(ℝ, Coordinates) : Space → Type) where
  inner := spaceInner
  symm S := coordinatePair_comm (coordinateChart S)
  pos S := coordinatePair_pos (coordinateChart S) (extract_mem S)
  isVonNBounded S := coordinatePair_isVonNBounded (coordinateChart S) (extract_mem S)
  contMDiff := contMDiff_spaceInner

end TernaryPoly.SymmetricSpaceTraceMetric
