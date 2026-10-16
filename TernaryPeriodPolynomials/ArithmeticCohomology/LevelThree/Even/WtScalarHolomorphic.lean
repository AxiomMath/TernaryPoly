module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalarCauchy
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Basic

@[expose] public section


/-!
# Holomorphy of the scalar weighted realization

Formalized by Claude Sonnet 5.5 (AxiomCode).

The scalar Cauchy formula of `WtScalarCauchy` exhibits `cuspScalarWeightedRealizationWt` near each
point of the upper half plane as a Cauchy transform of a continuous function on a circle, which is
a convergent power series (`hasFPowerSeriesOn_cauchy_integral`).  Hence the scalar weighted
realization is holomorphic whenever the Hilbert-space weighted orbit is.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped NNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.MultiplicityOne (levelThreeValues mem_levelThreeValues)

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

/-- **Holomorphy of the scalar weighted realization.**  If the weighted orbit of a smooth
finite-level fixed vector is holomorphic on the upper half plane, so is its scalar weighted
realization at every base point. -/
theorem cuspScalarWeightedRealization_holomorphicWt (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (wt : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    (base : BinaryAdelicGL) :
    DifferentiableOn ℂ (cuspScalarWeightedRealizationWt cusp wt vector base)
      UpperHalfPlane.upperHalfPlaneSet := by
  intro c center
  apply DifferentiableAt.differentiableWithinAt
  have center_positive : 0 < c.im := center
  obtain ⟨R, radius_positive, radius_small⟩ : ∃ R : ℝ≥0, 0 < R ∧ (R : ℝ) < c.im := by
    refine ⟨⟨c.im / 2, by linarith⟩, NNReal.coe_pos.mp ?_, ?_⟩
    · show (0 : ℝ) < c.im / 2
      linarith
    · show c.im / 2 < c.im
      linarith
  have radius_real : 0 < (R : ℝ) := NNReal.coe_pos.mpr radius_positive
  have on_circle : ContinuousOn (cuspScalarWeightedRealizationWt cusp wt vector base)
      (Metric.sphere c R) :=
    (cuspScalarWeightedRealization_analyticWt cusp wt vector base).continuousOn.mono
      (fun z member => wtCauchy_im_pos_of_dist_le radius_small (Metric.mem_sphere.mp member).le)
  have integrable : CircleIntegrable (cuspScalarWeightedRealizationWt cusp wt vector base) c R :=
    on_circle.circleIntegrable radius_real.le
  have transform : DifferentiableAt ℂ (fun w => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      circleIntegral (fun z => (z - w)⁻¹ •
        cuspScalarWeightedRealizationWt cusp wt vector base z) c R) c :=
    (hasFPowerSeriesOn_cauchy_integral integrable radius_positive).analyticAt.differentiableAt
  apply transform.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds c radius_real] with w member
  exact cuspScalarWeightedRealization_cauchyWt cusp stages wt vector fixed holomorphic
    radius_real radius_small member base

/-- The scalar weighted realization at the identity base point, on the upper half plane. -/
theorem cuspScalarWeightedRealization_holomorphicWt_one (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (wt : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector.val)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (cuspScalarWeightedRealizationWt cusp wt vector 1)
      UpperHalfPlane.upperHalfPlaneSet :=
  cuspScalarWeightedRealization_holomorphicWt cusp stages wt vector fixed holomorphic 1

/-- A vector fixed by the level-three Levi level is fixed by the principal congruence level. -/
theorem levelThreeValues_fixedLevelWt {cusp : CuspidalRepresentation} {vector : cusp.H}
    (hlev : vector ∈ levelThreeValues cusp) :
    vector ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence := by
  rintro ⟨element, compact, hcongr, rfl⟩
  have reduced : GeneralLinearGroup.map integralReduction compact = 1 := hcongr
  have in_level : PlaneLeviLevel compact := by
    unfold PlaneLeviLevel
    rw [reduced]
    simp
  exact mem_levelThreeValues.mp hlev compact in_level

/-- **Holomorphy for level-three weight vectors.** -/
theorem cuspScalarWeightedRealization_holomorphic_levelThreeWt (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (wt : ℤ) (vector : cusp.smooth)
    (hlev : vector.val ∈ levelThreeValues cusp)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    (base : BinaryAdelicGL) :
    DifferentiableOn ℂ (cuspScalarWeightedRealizationWt cusp wt vector base)
      UpperHalfPlane.upperHalfPlaneSet :=
  cuspScalarWeightedRealization_holomorphicWt cusp stages wt vector
    (levelThreeValues_fixedLevelWt hlev) holomorphic base

end TernaryPeriodPolynomials.EvenLevelThree
