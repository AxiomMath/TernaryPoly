module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad5
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Weight

@[expose] public section


/-!
# R-e: R-e, the guarded bad-plane identity

`badPlaneEntryIdentity`: `FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad` with `S.rBad = (1/9)·∏_{p≠3} c_p`; nothing is asserted off the good-line orbit. `badPlaneWeight_planeWeight`, `goodLineWeight_lineWeight` give K's `PlaneWeight`/`LineWeight` structures.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The bad-plane weight is a plane weight. -/
theorem badPlaneWeight_planeWeight : PlaneWeight badPlaneWeight :=
  ⟨badPlaneWeight_finite, fun k g => badPlaneWeight_level k g, fun p hp g => badPlaneWeight_parabolic p hp g⟩

/-- The good-line weight is a line weight. -/
theorem goodLineWeight_lineWeight : LineWeight goodLineWeight :=
  ⟨goodLineWeight_finite, fun k g => goodLineWeight_level k g, fun p hp g => goodLineWeight_parabolic p hp g⟩

open Classical in
theorem badPlaneWeight_norm_le (g : AdelicGL) : ‖badPlaneWeight g‖ ≤ 1 := by
  unfold badPlaneWeight
  split_ifs <;> simp

open Classical in
theorem goodLineWeight_goodLineSet {g : AdelicGL} (h : goodLineWeight g ≠ 0) :
    goodLineSet (GeneralLinearGroup.map finiteThree (finiteGroup g)) := by
  unfold goodLineWeight at h
  by_contra no
  exact h (ite_eq_right no)

namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)

include S

/-- **The scalar `r` of the bad-plane finite entry** at the good-line cusp: `1/9` times the product of the local
Euler factors away from `3`, i.e. `(1/9) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`. -/
def rBad : ℂ := S.value * (1 / 9 : ℂ)

end SphericalEntryData

open Classical in
/-- **R-e, bad plane at the good line.**  For the bad-plane section (weight `ιP`, the indicator of `P(ℚ₃)K₁`) the
finite entry identity holds at every `g` in the good-line orbit `L(ℚ₃) g₀ K₁` (weight `ιL`), with
`r = (1/9) · ∏_{p ≠ 3} c_p`. -/
theorem badPlaneEntryIdentity {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) :
    FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad := by
  intro g hg x
  have hgood := goodLineWeight_goodLineSet hg
  have convergent := S.exponent_gt
  have integrand : ∀ (v : FiniteAdeles × FiniteAdeles) (z : ℂ),
      badPlaneWeight (finiteEntryElement v g) *
        (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z) =
      badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g)) *
        planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) S.halfWeight S.vector x
          (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g) z := by
    intro v z
    have weight : badPlaneWeight (finiteEntryElement v g) =
        badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g)) := by
      apply badPlaneWeight_finite
      rw [finiteGroup_entryElement, finiteGroup_atFinite]
    rw [weight]
    congr 1
    exact (cF_mul_F_eq_planeCoeff D S.halfWeight S.vector x (finiteEntryElement v g) z).trans
      (by rw [finiteGroup_entryElement])
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [integrand]
    exact ((badPlaneWeight_radical_measurable (finiteGroup g) hgood).comp measurable_fst).mul
      (planeCoeff_measurable D.cusp D.chi _ S.halfWeight S.hχ S.vector S.spherical x (finiteGroup g))
  · intro Z hZ hZ'
    obtain ⟨φ, hφ, bound⟩ := planeCoeff_majorant D.cusp D.chi _ S.halfWeight S.hχ S.vector S.spherical
      convergent x (finiteGroup g) Z hZ hZ'
    refine ⟨φ, hφ, fun v z hz => ?_⟩
    rw [integrand, norm_mul]
    calc ‖badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g))‖ *
          ‖planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) S.halfWeight S.vector x
            (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g) z‖
        ≤ 1 * φ v := mul_le_mul (badPlaneWeight_norm_le _) (bound v z hz) (norm_nonneg _) zero_le_one
      _ = φ v := one_mul _
  · intro z _
    simp_rw [integrand]
    have lhs : (∫ v : FiniteAdeles × FiniteAdeles, badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 *
        finiteGroup g)) * planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) S.halfWeight S.vector x
          (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g) z ∂(finiteMeasure.prod finiteMeasure)) =
        ((z.im ^ S.halfWeight : ℝ) : ℂ) * entryPlaneIntegral D.cusp D.chi (((n : ℂ) + 3) / 2)
          (fun h => badPlaneWeight (atFinite h)) S.vector.val (finiteGroup g)
          (x * atInfinity (sectionMatrix z)) := by
      simp_rw [planeCoeff_eq]
      unfold entryPlaneIntegral
      rw [← integral_const_mul]
      congr 1
      funext v
      ring
    rw [lhs, entryPlaneIntegral_bad_general D.cusp D.chi _ S.hχ S.vector S.nonzero S.spherical convergent
      S.localEigenvalue (fun place _ => S.eigen_place place) S.value S.product (finiteGroup g) hgood]
    unfold SphericalEntryData.rBad SphericalEntryData.F
    rw [cFLine_mul_F_eq_lineCoeff]
    have : (((n : ℂ) + 3) / 2 - 1) = TernaryPeriodPolynomials.SourceConstruction.lineBeta n := by
      unfold TernaryPeriodPolynomials.SourceConstruction.lineBeta; ring
    rw [this, lineCoeff_eq]
    ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
