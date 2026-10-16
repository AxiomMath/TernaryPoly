module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FiniteAveragedFormCusp

@[expose] public section


/-!
# Finite averages of the pointwise Eichler normal form

Let `F = F_v` be the scalar weighted realization of a spherical smooth vector `v` and let
`F_avg` be its finite good-line average at the real component of the adelic point. At a point
`b(f) g` with `g` real, the weighted Eichler period `w(f) Per_F(z)(b(f) g)` is the integral over
the straight path of the averaged path integrand, which is continuous in the finite pair and the
path parameter and integrable on the product. Hence the weighted scalar tests of the Eichler
period and of the pointwise Eichler normal form are continuous and integrable in the finite pair,
and their integrals are the corresponding scalar tests of the Eichler period and of the
pointwise normal form of `F_avg` at `g` (Fubini over the finite pair and the path parameter).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

section Spherical

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (spherical : vector.val ∈ cuspSphericalValues cusp)

include spherical in
/-- The standard and the `p`-adic weighted values of the scalar weighted realization agree. -/
theorem cuspScalar_weight_eq_padic (g : BinaryRealGL) (w : ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        cuspScalarWeightedRealization cusp halfWeight vector
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) w =
      finiteAverageWeight ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite *
        cuspScalarWeightedRealization cusp halfWeight vector
          (atFinite (finiteAverageBlock finite) * atInfinity g) w := by
  rw [cuspScalar_averagedIntegrand_eq cusp halfWeight vector spherical,
    ← cuspScalarAffineRealization_eq_integrand]
  simp only [cuspScalarWeightedRealization, Complex.real_smul]
  ring

include spherical in
/-- The weighted clamped Eichler integrand is the averaged path integrand. -/
theorem weighted_clampedIntegrand_eq (g : BinaryRealGL) (z : ℂ) (j : Fin (n + 2))
    (finite : FiniteAwayThree × FiniteAwayThree) (t : ℝ) :
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        clampedIntegrand n (cuspScalarWeightedRealization cusp halfWeight vector) z
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) j t =
      averagedPathIntegrand cusp halfWeight vector ((n : ℂ) / 2 + 3 + cohomologicalPoint) g z j
        (finite, t) := by
  rw [averagedPathIntegrand_eq_clamped]
  simp only [clampedIntegrand]
  linear_combination (z - Complex.I) *
    (binaryWeightBasis (n + 1)).coord j (binaryPointPower (n + 1) (clampedPath z t)) *
    cuspScalar_weight_eq_padic (n := n) cusp halfWeight vector spherical g (clampedPath z t) finite

include spherical in
/-- **The weighted coordinates of the Eichler period** of `F_v` at `b(f) g` are continuous and
integrable in the finite pair, with integral the coordinate of the Eichler period of `F_avg`. -/
theorem weighted_coord_eichlerPeriod (large : 3 < n) (g : BinaryRealGL) {z : ℂ}
    (positive : 0 < z.im) (j : Fin (n + 2)) :
    Continuous (fun finite : FiniteAwayThree × FiniteAwayThree =>
        standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
            (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))) ∧
      Integrable (fun finite : FiniteAwayThree × FiniteAwayThree =>
        standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
            (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)))
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
            (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
        (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
          (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)) z
          (atInfinity g)) := by
  set e : ℂ := (n : ℂ) / 2 + 3 + cohomologicalPoint
  have convergent : 3 < e.re := cohomologicalExponent_re large
  have pointwise (finite : FiniteAwayThree × FiniteAwayThree) :
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
            (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)) =
        ∫ t in (0 : ℝ)..1, averagedPathIntegrand cusp halfWeight vector e g z j (finite, t) := by
    rw [coord_eichlerPeriod_clamped, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ =>
      weighted_clampedIntegrand_eq cusp halfWeight vector spherical g z j finite t
  have product := averagedPathIntegrand_integrable cusp halfWeight vector e g z j positive
    spherical convergent
  refine ⟨?_, ?_, ?_⟩
  · simp only [pointwise]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun finite t => averagedPathIntegrand cusp halfWeight vector e g z j (finite, t))
      (averagedPathIntegrand_continuous cusp halfWeight vector e g z j positive spherical) 0 1
  · simp only [pointwise, intervalIntegral.integral_of_le zero_le_one]
    exact product.integral_prod_left
  · simp only [pointwise, intervalIntegral.integral_of_le zero_le_one]
    rw [integral_integral_swap (f := fun finite t =>
      averagedPathIntegrand cusp halfWeight vector e g z j (finite, t)) product,
      coord_eichlerPeriod_clamped, intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [] with t
    have back (finite : FiniteAwayThree × FiniteAwayThree) :
        averagedPathIntegrand cusp halfWeight vector e g z j (finite, t) =
          standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
            clampedIntegrand n (cuspScalarWeightedRealization cusp halfWeight vector) z
              (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) j t :=
      (weighted_clampedIntegrand_eq cusp halfWeight vector spherical g z j finite t).symm
    simp only [back]
    simp only [clampedIntegrand, averagedRealForm_atInfinity, averagedForm_def]
    rw [← integral_const_mul, ← integral_mul_const]
    congr 1
    funext finite
    ring

include spherical in
/-- **The weighted scalar tests of the Eichler period** of `F_v` at `b(f) g` are continuous and
integrable in the finite pair, with integral the scalar test of the Eichler period of `F_avg`. -/
theorem weighted_functional_eichlerPeriod (large : 3 < n) (g : BinaryRealGL) {z : ℂ}
    (positive : 0 < z.im) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun finite : FiniteAwayThree × FiniteAwayThree =>
        standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))) ∧
      Integrable (fun finite : FiniteAwayThree × FiniteAwayThree =>
        standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)))
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
        functional (eichlerPeriod n
          (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)) z
          (atInfinity g)) := by
  have coordinate := weighted_coord_eichlerPeriod cusp halfWeight vector spherical large g positive
  have expansion (finite : FiniteAwayThree × FiniteAwayThree) :
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)) =
        ∑ j, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
            (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)) *
          functional (binaryWeightBasis (n + 1) j) := by
    rw [functional_eq_sum_coord functional, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [expansion]
  refine ⟨continuous_finsetSum _ fun j _ => (coordinate j).1.mul continuous_const,
    integrable_finsetSum _ fun j _ => (coordinate j).2.1.mul_const _, ?_⟩
  rw [integral_finsetSum _ fun j _ => (coordinate j).2.1.mul_const _,
    functional_eq_sum_coord functional]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_mul_const, (coordinate j).2.2]

theorem atFinite_mul_atInfinity_mul (block : BinaryFiniteGL) (g k : BinaryRealGL) :
    atFinite block * atInfinity g * atInfinity k = atFinite block * atInfinity (g * k) := by
  rw [mul_assoc, atInfinity_mul]

include spherical in
/-- **The weighted scalar tests of the pointwise Eichler normal form** of `F_v` at `b(f) g` are
continuous and integrable in the finite pair, with integral the scalar test of the pointwise
Eichler normal form of `F_avg` at `g`. -/
theorem weighted_functional_eichlerNormal (large : 3 < n) (A g : BinaryRealGL)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun finite : FiniteAwayThree × FiniteAwayThree =>
        standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector) A
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))) ∧
      Integrable (fun finite : FiniteAwayThree × FiniteAwayThree =>
        standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector) A
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)))
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector) A
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
        functional (eichlerNormal n
          (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)) A
          (atInfinity g)) := by
  have direct := weighted_functional_eichlerPeriod cusp halfWeight vector spherical large g
    (A • UpperHalfPlane.I).im_pos functional
  have reflected := weighted_functional_eichlerPeriod cusp halfWeight vector spherical large
    (g * UpperHalfPlane.J) (reflectUpper (A • UpperHalfPlane.I)).im_pos
    (reflectedFunctional functional)
  have expansion (finite : FiniteAwayThree × FiniteAwayThree) :
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector) A
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)) =
        (2 : ℂ)⁻¹ * (standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
            functional (eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector)
              ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)
              (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)) +
          standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
            reflectedFunctional functional (eichlerPeriod n
              (cuspScalarWeightedRealization cusp halfWeight vector)
              (reflectUpper (A • UpperHalfPlane.I) : ℂ)
              (atFinite (standardGoodLineFiniteCoordinates finite).block *
                atInfinity (g * UpperHalfPlane.J)))) := by
    rw [functional_eichlerNormal, atFinite_mul_atInfinity_mul]
    ring
  simp only [expansion]
  refine ⟨continuous_const.mul (direct.1.add reflected.1),
    (direct.2.1.add reflected.2.1).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add direct.2.1 reflected.2.1, direct.2.2, reflected.2.2,
    functional_eichlerNormal, atInfinity_mul]

end Spherical

end TernaryPeriodPolynomials.AnalyticClasses
