module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.RealizeIntervalIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalar

@[expose] public section


/-!
# The Cauchy formula for the scalar weighted realization

Formalized by Claude Sonnet 5.5 (AxiomCode).

For a smooth finite-level fixed vector whose weighted orbit `O` is holomorphic on the upper half
plane, the Hilbert-space Cauchy formula `O w = (2πi)⁻¹ ∮ (z - w)⁻¹ • O z` on a circle inside the
upper half plane is a Bochner integral along a continuous path of real matrices.  The
commutation of the (non-continuous) realization with such path integrals
(`AnalyticClasses.commutesOn_of_continuous`) turns it into the scalar Cauchy formula for
`cuspScalarWeightedRealizationWt`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.AnalyticClasses (commutesOn_of_continuous)

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

theorem wtCauchy_im_pos_of_dist_le {c z : ℂ} {R : ℝ} (hR : R < c.im) (hz : dist z c ≤ R) :
    0 < z.im := by
  have bound : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
  rw [Complex.dist_eq] at hz
  have lower : -|(z - c).im| ≤ (z - c).im := neg_abs_le _
  have difference : (z - c).im = z.im - c.im := Complex.sub_im z c
  linarith [bound, lower, hz, difference]

theorem wtCauchy_circle_im_pos {c : ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hR : R < c.im) (t : ℝ) :
    0 < (circleMap c R t).im :=
  wtCauchy_im_pos_of_dist_le hR (Metric.mem_sphere.mp (circleMap_mem_sphere c hR0 t)).le

theorem wtCauchy_circle_sub_ne {c w : ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hw : w ∈ Metric.ball c R)
    (t : ℝ) : circleMap c R t - w ≠ 0 := by
  intro zero
  have same : circleMap c R t = w := sub_eq_zero.mp zero
  have on_circle := Metric.mem_sphere.mp (circleMap_mem_sphere c hR0 t)
  have inside := Metric.mem_ball.mp hw
  rw [same] at on_circle
  rw [on_circle] at inside
  exact lt_irrefl _ inside

/-- The scalar weight of the Cauchy integrand along the circle `circleMap c R`. -/
def cauchyCoefficientWt (wt : ℤ) (c w : ℂ) (R : ℝ) (t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (circleMap 0 R t * Complex.I *
    ((circleMap c R t - w)⁻¹ * ((wtFactor wt (circleMap c R t).im : ℝ) : ℂ)))

theorem cauchyCoefficientWt_continuous (wt : ℤ) {c w : ℂ} {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < c.im) (hw : w ∈ Metric.ball c R) : Continuous (cauchyCoefficientWt wt c w R) := by
  have hcm : Continuous (circleMap c R) := continuous_circleMap c R
  have hcm0 : Continuous (circleMap 0 R) := continuous_circleMap 0 R
  have hinv : Continuous fun t => (circleMap c R t - w)⁻¹ :=
    (hcm.sub continuous_const).inv₀ (fun t => wtCauchy_circle_sub_ne hR0 hw t)
  have hwf : Continuous fun t => wtFactor wt (circleMap c R t).im := by
    rw [continuous_iff_continuousAt]
    intro t
    have outer : ContinuousAt (wtFactor wt) (circleMap c R t).im :=
      wtFactor_continuousAt wt (wtCauchy_circle_im_pos hR0 hR t)
    have inner : ContinuousAt (fun s : ℝ => (circleMap c R s).im) t :=
      (Complex.continuous_im.comp hcm).continuousAt
    exact ContinuousAt.comp (g := wtFactor wt) (f := fun s : ℝ => (circleMap c R s).im)
      outer inner
  have product : Continuous fun t => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (circleMap 0 R t * Complex.I *
        ((circleMap c R t - w)⁻¹ * ((wtFactor wt (circleMap c R t).im : ℝ) : ℂ))) :=
    continuous_const.mul ((hcm0.mul continuous_const).mul
      (hinv.mul (Complex.continuous_ofReal.comp hwf)))
  exact product

/-- The Hilbert-space Cauchy formula for the weighted affine orbit on a disc in the upper half
plane. -/
theorem cuspWeightedAffineOrbitWt_cauchy (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector)
      UpperHalfPlane.upperHalfPlaneSet)
    {c w : ℂ} {R : ℝ} (hR : R < c.im) (hw : w ∈ Metric.ball c R) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        circleIntegral (fun z => (z - w)⁻¹ • cuspWeightedAffineOrbitWt cusp wt vector z) c R =
      cuspWeightedAffineOrbitWt cusp wt vector w := by
  have inside : closure (Metric.ball c R) ⊆ UpperHalfPlane.upperHalfPlaneSet := fun z hz =>
    wtCauchy_im_pos_of_dist_le hR
      (Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hz))
  exact (holomorphic.mono inside).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

/-- Along the circle, the Cauchy-weighted realized translates integrate to the weighted orbit. -/
theorem integral_cauchyCoefficientWt_smul_realOrbit (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    {c w : ℂ} {R : ℝ} (hR : R < c.im) (hw : w ∈ Metric.ball c R) :
    (∫ t in (0 : ℝ)..2 * Real.pi, cauchyCoefficientWt wt c w R t •
        OrbitTranslation.realOrbit cusp vector.val
          (binaryUpperSectionMatrix (circleMap c R t))) =
      cuspWeightedAffineOrbitWt cusp wt vector.val w := by
  rw [← cuspWeightedAffineOrbitWt_cauchy cusp wt vector.val holomorphic hR hw]
  unfold circleIntegral
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [cuspWeightedAffineOrbitWt, deriv_circleMap, ← Complex.coe_smul, smul_smul]
  rfl

/-- The scalar side of the Cauchy integral, as the integral of the coefficient times the
realization of a translate. -/
theorem integral_cauchyCoefficientWt_mul_realize (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (c w : ℂ) (R : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, cauchyCoefficientWt wt c w R t *
        cusp.realize vector (base * atInfinity
          (invertibleMatrix (binaryUpperSectionMatrix (circleMap c R t))))) =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        circleIntegral (fun z => (z - w)⁻¹ •
          cuspScalarWeightedRealizationWt cusp wt vector base z) c R := by
  unfold circleIntegral
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [cauchyCoefficientWt, cuspScalarWeightedRealizationWt, cuspScalarAffineRealization,
    deriv_circleMap, Complex.real_smul, smul_eq_mul]
  ring

/-- A smooth vector whose underlying vector is the weighted orbit at `z` has the scalar weighted
realization at `z`. -/
theorem realize_eq_scalarWeightedRealizationWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth) (z : ℂ) (w : cusp.smooth)
    (hval : w.val = cuspWeightedAffineOrbitWt cusp wt vector.val z) (base : BinaryAdelicGL) :
    cusp.realize w base = cuspScalarWeightedRealizationWt cusp wt vector base z := by
  have hw : w = ((wtFactor wt z.im : ℝ) : ℂ) •
      (⟨cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix z))) vector.val,
        cusp.smooth_stable _ _ vector.property⟩ : cusp.smooth) := by
    apply Subtype.ext
    rw [hval, cuspWeightedAffineOrbitWt, ← Complex.coe_smul]
    rfl
  rw [hw, map_smul, Pi.smul_apply, cusp.equivariant, smul_eq_mul]
  simp only [cuspScalarWeightedRealizationWt, cuspScalarAffineRealization, Complex.real_smul]

/-- **The scalar Cauchy formula.**  On a disc `ball c R` with `R < Im c`, the scalar weighted
realization of a smooth finite-level fixed vector with holomorphic weighted orbit is the Cauchy
integral of its values on the boundary circle. -/
theorem cuspScalarWeightedRealization_cauchyWt (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (wt : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    {c w : ℂ} {R : ℝ} (hR0 : 0 < R) (hR : R < c.im) (hw : w ∈ Metric.ball c R)
    (base : BinaryAdelicGL) :
    cuspScalarWeightedRealizationWt cusp wt vector base w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        circleIntegral (fun z => (z - w)⁻¹ •
          cuspScalarWeightedRealizationWt cusp wt vector base z) c R := by
  have continuousPath : Continuous (fun t => binaryUpperSectionMatrix (circleMap c R t)) :=
    (binaryUpperSectionMatrix_contDiffOn (order := 0)).continuousOn.comp_continuous
      (continuous_circleMap c R) (fun t => wtCauchy_circle_im_pos hR0.le hR t)
  obtain ⟨smoothVector, hvalue, hrealize⟩ := commutesOn_of_continuous cusp stages vector fixed
    (fun t => binaryUpperSectionMatrix (circleMap c R t)) (cauchyCoefficientWt wt c w R)
    continuousPath (cauchyCoefficientWt_continuous wt hR0.le hR hw)
    (fun t => binaryUpperSectionMatrix_invertible _ (wtCauchy_circle_im_pos hR0.le hR t))
    0 (2 * Real.pi) (by positivity)
  have hval : smoothVector.val = cuspWeightedAffineOrbitWt cusp wt vector.val w := by
    rw [hvalue]
    exact integral_cauchyCoefficientWt_smul_realOrbit cusp wt vector holomorphic hR hw
  rw [← realize_eq_scalarWeightedRealizationWt cusp wt vector w smoothVector hval base,
    hrealize base]
  exact integral_cauchyCoefficientWt_mul_realize cusp wt vector base c w R

end TernaryPeriodPolynomials.EvenLevelThree
