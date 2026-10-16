module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.AdditiveDomain
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Scaling
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalNorm

@[expose] public section


/-!
# Rational scaling of periodic adelic integrals

For a `ℚ`-periodic function `Ψ` on the adeles and `c ∈ ℚˣ`, the integral of `u ↦ Ψ (c u)` over
the fundamental domain `[0,1) × Ẑ` equals the integral of `Ψ`: multiplication by `c` preserves the
Haar measure and carries the fundamental domain to another fundamental domain.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalAdditiveDomain

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization

/-- Multiplication by a rational unit, as a topological additive equivalence of the adeles. -/
def scalingEquiv (c : ℚˣ) : Adeles ≃ₜ+ Adeles :=
  ContinuousAddEquiv.mulLeft (Units.map rationalAdele c)

theorem scalingEquiv_apply (c : ℚˣ) (v : Adeles) :
    scalingEquiv c v = rationalAdele c.val * v := rfl

theorem scalingEquiv_measurePreserving (c : ℚˣ) :
    MeasurePreserving (scalingEquiv c) adeleMeasure adeleMeasure := by
  refine ⟨(scalingEquiv c).continuous.measurable, ?_⟩
  have h := Helpers.adeleNorm_smul_map (Units.map rationalAdele c)
  rw [Helpers.adeleNorm_rational, one_smul] at h
  exact h

theorem scalingEquiv_rational (c : ℚˣ) (q : ℚ) (v : Adeles) :
    scalingEquiv c (q +ᵥ v) = (c.val * q) +ᵥ scalingEquiv c v := by
  change rationalAdele c.val * (rationalAdele q + v) =
    rationalAdele (c.val * q) + rationalAdele c.val * v
  rw [mul_add, map_mul]

theorem scalingEquiv_image_fundamental (c : ℚˣ) :
    IsAddFundamentalDomain ℚ (scalingEquiv c '' additiveDomain) adeleMeasure := by
  refine RationalAdditiveDomain.domain_fundamental.image_of_equiv (scalingEquiv c).toEquiv ?_
    (c⁻¹).mulLeft ?_
  · exact ((scalingEquiv_measurePreserving c).symm
      (scalingEquiv c).toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving
  · intro q x
    change scalingEquiv c (((c⁻¹ : ℚˣ) : ℚ) * q +ᵥ x) = q +ᵥ scalingEquiv c x
    rw [scalingEquiv_rational, Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ c.ne_zero]

theorem rational_periodic_integral_scaling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : Adeles → E) (periodic : ∀ q : ℚ, ∀ v, Ψ (rationalAdele q + v) = Ψ v) (c : ℚˣ) :
    (∫ u in additiveDomain, Ψ (rationalAdele c.val * u) ∂adeleMeasure) =
      ∫ u in additiveDomain, Ψ u ∂adeleMeasure := by
  calc
    _ = ∫ u in scalingEquiv c '' additiveDomain, Ψ u ∂adeleMeasure :=
      ((scalingEquiv_measurePreserving c).setIntegral_image_emb
        (scalingEquiv c).toHomeomorph.measurableEmbedding Ψ additiveDomain).symm
    _ = _ := (scalingEquiv_image_fundamental c).setIntegral_eq
      RationalAdditiveDomain.domain_fundamental (fun q x => periodic q x)

theorem rational_periodic_integrableOn_scaling {E : Type*} [NormedAddCommGroup E]
    (Ψ : Adeles → E) (periodic : ∀ q : ℚ, ∀ v, Ψ (rationalAdele q + v) = Ψ v) (c : ℚˣ) :
    IntegrableOn (fun u => Ψ (rationalAdele c.val * u)) additiveDomain adeleMeasure ↔
      IntegrableOn Ψ additiveDomain adeleMeasure := by
  have h1 := (scalingEquiv_measurePreserving c).integrableOn_image
    (scalingEquiv c).toHomeomorph.measurableEmbedding (s := additiveDomain) (f := Ψ)
  exact h1.symm.trans ((scalingEquiv_image_fundamental c).integrableOn_iff
    RationalAdditiveDomain.domain_fundamental (fun q x => periodic q x))

end TernaryPeriodPolynomials.CuspIntegral
