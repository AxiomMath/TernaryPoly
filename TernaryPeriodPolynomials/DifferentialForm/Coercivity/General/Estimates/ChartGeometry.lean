module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.RiemannianProper
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Isometries
public import TernaryPeriodPolynomials.DifferentialForm.Connection.RiemannianSplit
public import Mathlib.Geometry.Manifold.Riemannian.Basic

@[expose] public section


/-! # General coercivity, Tier B: lengths of chart segments in the covering space

The Riemannian distance of two points of the covering space is bounded by the length element along
the straight segment joining their coordinates.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceRiemannian
  TernaryPoly.SymmetricSpaceTraceMetric TernaryPoly.SymmetricSpaceQuotientManifold Manifold Bundle Set
open scoped ContDiff Manifold Bundle SymmetricSpaceRiemannian Topology

section Generic

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [EMetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

/-- The Riemannian distance between the endpoints of a straight segment is bounded by a bound for
the length element along the segment. -/
theorem edist_le_of_segment_bound {U : Set F} (hU : IsOpen U)
    {f : F → M} (hf : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 f U) {x y : F}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x y t ∈ U)
    {B : ℝ≥0∞} (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f (AffineMap.lineMap x y t) (y - x)‖ₑ ≤ B) :
    edist (f x) (f y) ≤ B := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have h1 : (η : ℝ → F) = AffineMap.lineMap x y := ContinuousAffineMap.coe_lineMap_eq ..
  have hη : Set.MapsTo η (Icc (0 : ℝ) 1) U := fun t ht => by
    rw [h1]
    exact hseg t ht
  have hηsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 η (Icc (0 : ℝ) 1) := by
    exact (contMDiff_iff_contDiff.mpr η.contDiff).contMDiffOn
  have hlen : edist (f x) (f y) ≤ pathELength 𝓘(ℝ, E) (f ∘ η) 0 1 := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, E))]
    apply riemannianEDist_le_pathELength (hf.comp hηsmooth hη)
    · simp [η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [η, ContinuousAffineMap.coe_lineMap_eq]
    · exact zero_le_one
  apply hlen.trans
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  calc ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f ∘ η) (Icc (0 : ℝ) 1) t 1‖ₑ
      ≤ ∫⁻ t in Icc (0 : ℝ) 1, B := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        have hd := (hf (η t) (hη ht)).mdifferentiableWithinAt one_ne_zero
        have he : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f ∘ η) (Icc (0 : ℝ) 1) t =
            (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) f (η t)) ∘L
              mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (Icc (0 : ℝ) 1) t := by
          rw [← mfderivWithin_of_mem_nhds (hU.mem_nhds (hη ht))]
          apply mfderivWithin_comp
          · exact hd
          · exact hηsmooth.mdifferentiableOn one_ne_zero t ht
          · exact hη
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc zero_lt_one t ht
        rw [he, ContinuousLinearMap.comp_apply]
        convert! hb t ht using 3
        congr 1
        rw [mfderivWithin_eq_fderivWithin]
        rw [h1]
        exact (AffineMap.hasDerivWithinAt_lineMap (𝕜 := ℝ)).derivWithin
          (uniqueDiffOn_Icc zero_lt_one t ht)
    _ = B := by simp


end Generic

theorem contMDiffOn_chartSymm :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) ∞ coordinateChart.symm positiveCoordinates := by
  have h := (contMDiffOn_chart_symm (I := 𝓘(ℝ, Coordinates)) (n := ∞)
    (x := (coordinateChart.symm (0 : Coordinates))))
  rw [space_chartAt, coordinateChart_target] at h
  exact h

theorem mdifferentiableAt_chartSymm {z : Coordinates} (hz : z ∈ positiveCoordinates) :
    MDifferentiableAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) coordinateChart.symm z :=
  ((contMDiffOn_chartSymm.contMDiffAt (isOpen_positiveCoordinates.mem_nhds hz)).mdifferentiableAt
    (by simp))

theorem mfderiv_chartSymm {z : Coordinates} (hz : z ∈ positiveCoordinates) (w : Coordinates) :
    mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) coordinateChart.symm z w = w := by
  rw [(mdifferentiableAt_chartSymm hz).mfderiv]
  have hev : writtenInExtChartAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) z
      (coordinateChart.symm : Coordinates → Space) =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hz] with u hu
    have hu' : u ∈ coordinateChart.target := by rw [coordinateChart_target]; exact hu
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, Function.comp_apply,
      PartialEquiv.refl_coe, id_eq, PartialEquiv.refl_symm]
    exact congrArg (fun p => p) (coordinateChart.right_inv hu')
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  have hz0 : (extChartAt 𝓘(ℝ, Coordinates) z) z = z := by
    simp [chartAt_self_eq]
  rw [hz0, hev.fderiv_eq, fderiv_id]
  rfl


attribute [local instance] spaceMetricSpace

theorem enorm_mfderiv_chartSymm {z : Coordinates} (hz : z ∈ positiveCoordinates) (w : Coordinates) :
    ‖mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) coordinateChart.symm z w‖ₑ =
      ENNReal.ofReal (Real.sqrt (coordinatePair z w w)) := by
  have hz' : z ∈ coordinateChart.target := by rw [coordinateChart_target]; exact hz
  let v : TangentSpace 𝓘(ℝ, Coordinates) (coordinateChart.symm z) := w
  have e : mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) coordinateChart.symm z w = v :=
    mfderiv_chartSymm hz w
  have h1 : inner ℝ v v = coordinatePair z w w := by
    change coordinatePair (coordinateChart (coordinateChart.symm z)) w w = _
    rw [coordinateChart.right_inv hz']
  have hn : ‖v‖ = Real.sqrt (coordinatePair z w w) := by
    rw [norm_eq_sqrt_real_inner v, h1]
  rw [e, ← ofReal_norm, hn]

/-- The Riemannian distance of two chart points is at most a bound for the length element along the
straight segment joining them. -/
theorem dist_chart_le {y₁ y₂ : Coordinates}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap y₁ y₂ t ∈ positiveCoordinates) {B : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      Real.sqrt (coordinatePair (AffineMap.lineMap y₁ y₂ t) (y₂ - y₁) (y₂ - y₁)) ≤ B) :
    dist (coordinateChart.symm y₁ : Space) (coordinateChart.symm y₂) ≤ B := by
  have hB : 0 ≤ B := (Real.sqrt_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hmain := edist_le_of_segment_bound (E := Coordinates) (F := Coordinates) (M := Space)
    isOpen_positiveCoordinates (contMDiffOn_chartSymm.of_le (by simp)) hseg (B := ENNReal.ofReal B)
    (fun t ht => by
      rw [enorm_mfderiv_chartSymm (hseg t ht)]
      exact ENNReal.ofReal_le_ofReal (hb t ht))
  rw [edist_dist] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hmain

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
