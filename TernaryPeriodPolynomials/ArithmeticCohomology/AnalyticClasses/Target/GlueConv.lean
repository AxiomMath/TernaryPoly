module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.TransferPeriod
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.PeriodClassCocycle

@[expose] public section


/-!
# The twisted normal form of the averaged form is the finite average of the twisted normal form

Let `F = F_v` be the scalar weighted realization of a spherical smooth vector `v` and let
`F_avg` be its finite good-line average at the real component. At the identity, the twisted
Eichler normal form `N⁻` of `F_avg` is the finite average, with the `p`-adic weight
`‖det b‖^{n/2 + 3 + s₀}`, of the twisted Eichler normal form of `F`. The standard and the
`p`-adic weights agree on the weighted values of `F`, hence on the weighted coordinates of the
Eichler period, and the standard-weight average of the Eichler period of `F` is the Eichler
period of `F_avg`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

section Spherical

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (spherical : vector.val ∈ cuspSphericalValues cusp)

include spherical in
/-- The standard and the `p`-adic weighted coordinates of the Eichler period agree. -/
theorem weighted_coord_eichlerPeriod_eq_padic (g : BinaryRealGL) (z : ℂ) (j : Fin (n + 2))
    (finite : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
          (cuspScalarWeightedRealization cusp halfWeight vector) z
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)) =
      finiteAverageWeight ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite *
        (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
          (cuspScalarWeightedRealization cusp halfWeight vector) z
          (atFinite (finiteAverageBlock finite) * atInfinity g)) := by
  rw [coord_eichlerPeriod_clamped, coord_eichlerPeriod_clamped,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [weighted_clampedIntegrand_eq cusp halfWeight vector spherical g z j finite t,
    averagedPathIntegrand_eq_clamped]

include spherical in
/-- **The `p`-adic weighted coordinates of the Eichler period** of `F_v` at `b(f) g` are
integrable, with integral the coordinate of the Eichler period of `F_avg` at `g`. -/
theorem padic_coord_eichlerPeriod (large : 3 < n) (g : BinaryRealGL) {z : ℂ}
    (positive : 0 < z.im) (j : Fin (n + 2)) :
    Integrable (fun finite : FiniteAwayThree × FiniteAwayThree =>
        finiteAverageWeight ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite *
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
            (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (finiteAverageBlock finite) * atInfinity g)))
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      ∫ finite, finiteAverageWeight ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite *
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
            (cuspScalarWeightedRealization cusp halfWeight vector) z
            (atFinite (finiteAverageBlock finite) * atInfinity g))
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
        (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n
          (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)) z
          (atInfinity g)) := by
  have key := weighted_coord_eichlerPeriod cusp halfWeight vector spherical large g positive j
  simp only [weighted_coord_eichlerPeriod_eq_padic cusp halfWeight vector spherical] at key
  exact ⟨key.2.1, key.2.2⟩

include spherical in
/-- The finite average of the right translates of the Eichler period of `F_v` is the Eichler
period of `F_avg`. -/
theorem finiteAverageBinary_eichlerPeriod_averaged (large : 3 < n) (g : BinaryRealGL) {z : ℂ}
    (positive : 0 < z.im) :
    FiniteAverageIntegrable ((n : ℂ) / 2 + 3 + cohomologicalPoint) (fun h =>
        eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector) z
          (h * atInfinity g)) ∧
      finiteAverageBinary ((n : ℂ) / 2 + 3 + cohomologicalPoint) (fun h =>
        eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector) z
          (h * atInfinity g)) =
        eichlerPeriod n (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector))
          z (1 * atInfinity g) := by
  refine ⟨fun j =>
    (padic_coord_eichlerPeriod cusp halfWeight vector spherical large g positive j).1, ?_⟩
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro j
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, coord_finiteAverageBinary,
    one_mul]
  exact (padic_coord_eichlerPeriod cusp halfWeight vector spherical large g positive j).2

include spherical in
/-- **The twisted normal form of the averaged form at the identity is the finite average of the
twisted normal form** (`n > 3`). -/
theorem eichlerTwisted_averagedRealForm_eq (large : 3 < n) (A : BinaryRealGL) :
    eichlerTwisted n (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector))
        A 1 =
      finiteAverageBinary ((n : ℂ) / 2 + 3 + cohomologicalPoint)
        (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector) A) := by
  have reflected : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact basePoint_im_pos A
  have first := finiteAverageBinary_eichlerPeriod_averaged cusp halfWeight vector spherical large
    1 (basePoint_im_pos A)
  have second := finiteAverageBinary_eichlerPeriod_averaged cusp halfWeight vector spherical large
    UpperHalfPlane.J reflected
  rw [eichlerTwisted_eq_map_sub (cuspScalarWeightedRealization cusp halfWeight vector),
    finiteAverageBinary_map_sub first.1 second.1, first.2, second.2,
    eichlerTwisted_eq_map_sub]

end Spherical

end TernaryPeriodPolynomials.AnalyticClasses
