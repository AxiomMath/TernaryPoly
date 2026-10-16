module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricSpaceBundle
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricInvariant

@[expose] public section


/-! Smooth GL3 action and its literal metric-preserving manifold derivative. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Matrix.Norms.Elementwise Topology

theorem coordinateChart_act (g : RealGL) (S : Space) :
    coordinateChart (act g S) = coordinateAction g (coordinateChart S) :=
  chartHomeomorph_act g S

/-- The normalized congruence action is smooth on the actual covering manifold. -/
theorem contMDiff_act (g : RealGL) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) ∞ (act g) := by
  have hc : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) ∞
      (fun S : Space => coordinateAction g (coordinateChart S)) := by
    rw [← contMDiffOn_univ]
    exact (contDiffOn_coordinateAction g).contMDiffOn.comp
      coordinateChart_contMDiff.contMDiffOn (fun S _ => extract_mem S)
  have hh := coordinateChart_symm_contMDiffOn.comp hc.contMDiffOn
    (show Set.MapsTo (fun S : Space => coordinateAction g (coordinateChart S)) Set.univ
      coordinateChart.target from fun S _ => by
        rw [coordinateChart_target]
        exact coordinateAction_mem g _ (extract_mem S))
  rw [contMDiffOn_univ] at hh
  apply hh.congr
  intro S
  change act g S = coordinateChart.symm (coordinateAction g (coordinateChart S))
  rw [← coordinateChart_act, coordinateChart.left_inv (by rw [coordinateChart_source]; trivial)]

/-- The manifold derivative is exactly the coordinate derivative. -/
theorem mfderiv_act (g : RealGL) (S : Space) :
    mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (act g) S =
      fderiv ℝ (coordinateAction g) (coordinateChart S) := by
  have h : HasMFDerivAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (act g) S
      (fderiv ℝ (coordinateAction g) (coordinateChart S)) := by
    refine ⟨(continuous_act g).continuousAt, ?_⟩
    simp only [modelWithCornersSelf_coe, Set.range_id]
    change HasFDerivWithinAt (coordinateChart ∘ act g ∘ coordinateChart.symm)
      (fderiv ℝ (coordinateAction g) (coordinateChart S)) Set.univ (coordinateChart S)
    have hd := ((contDiffOn_coordinateAction g).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds (extract_mem S))).differentiableAt (by simp)
    apply HasFDerivAt.hasFDerivWithinAt
    apply hd.hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [isOpen_positiveCoordinates.mem_nhds (extract_mem S)] with x hx
    simp only [Function.comp_apply, coordinateChart_act]
    rw [coordinateChart.right_inv (coordinateChart_target.symm ▸ hx)]
  exact h.mfderiv

/-- Every actual GL3 action preserves the smooth covering tangent metric. -/
theorem spaceInner_mfderiv_act (g : RealGL) (S : Space)
    (v w : TangentSpace 𝓘(ℝ, Coordinates) S) :
    spaceInner (act g S)
      (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (act g) S v)
      (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (act g) S w) = spaceInner S v w := by
  simp only [spaceInner_apply, mfderiv_act, coordinateChart_act]
  exact coordinatePair_fderiv_invariant g _ (extract_mem S) v w

end TernaryPoly.SymmetricSpaceTraceMetric
