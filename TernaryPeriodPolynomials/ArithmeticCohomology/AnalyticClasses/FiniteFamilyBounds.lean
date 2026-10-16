module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.SourceValueBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteAnalytic

@[expose] public section


/-!
# Holomorphic families of finite good-line integrals

For a spherical vector `w`, the finite good-line integral is
`G(s) = ∫ exp((n/2 + 3 + s) L) · w(b)`, an exponential family in `s`. This module records the
exponential form, the bound by the positive weight times the sup-norm of `w`, a bound locally
uniform in `s`, and Cauchy bounds for the `s`-derivative.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Metric

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The finite exponent attached to the standard parameter. -/
def finiteExponent (n : ℕ) (s : ℂ) : ℂ := (n : ℂ) / 2 + 3 + s

theorem finiteExponent_re (n : ℕ) (s : ℂ) : (finiteExponent n s).re = (n : ℝ) / 2 + 3 + s.re := by
  simp [finiteExponent]

/-- Exponential form of the finite good-line integral of a spherical vector. -/
theorem goodLineFiniteVectorIntegral_eq_exp (cusp : CuspidalRepresentation) (s : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    goodLineFiniteVectorIntegral n cusp s vector =
      ∫ pair, Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm pair : ℂ)) *
        cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun pair =>
    (goodLineFinitePadicIntegrand_eq n cusp s vector spherical pair).trans
      (goodLineFinitePadicIntegrand_eq_exp cusp vector _ pair))

/-- The positive weight integral, as a function of the real exponent. -/
def weightMass (e : ℝ) : ℝ :=
  ∫ pair, Real.exp (e * goodLineFiniteLogNorm pair) ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

theorem norm_cexp_mul_ofReal (z : ℂ) (x : ℝ) : ‖Complex.exp (z * (x : ℂ))‖ = Real.exp (z.re * x) := by
  rw [Complex.norm_exp]
  simp

/-- Bound by the weight mass times a uniform bound for the vector. -/
theorem norm_goodLineFiniteVectorIntegral_le (cusp : CuspidalRepresentation) (s : ℂ)
    (convergent : 3 < (finiteExponent n s).re)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (bound : ℝ) (bounded : ∀ argument, ‖cusp.realize vector argument‖ ≤ bound) :
    ‖goodLineFiniteVectorIntegral n cusp s vector‖ ≤ weightMass (finiteExponent n s).re * bound := by
  rw [goodLineFiniteVectorIntegral_eq_exp cusp s vector spherical, weightMass, ← integral_mul_const]
  apply norm_integral_le_of_norm_le
  · exact (goodLineFiniteLogNorm_exp_integrable _ convergent).mul_const _
  · filter_upwards [] with pair
    rw [norm_mul, norm_cexp_mul_ofReal]
    exact mul_le_mul_of_nonneg_left (bounded _) (Real.exp_pos _).le

/-- The exponential weight is dominated by its values at two bracketing exponents. -/
theorem exp_mul_le_add {e e₁ e₂ x : ℝ} (h₁ : e₁ ≤ e) (h₂ : e ≤ e₂) :
    Real.exp (e * x) ≤ Real.exp (e₁ * x) + Real.exp (e₂ * x) := by
  rcases le_total 0 x with hx | hx
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h₂ hx)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right h₁ hx)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

theorem weightMass_le {e e₁ e₂ : ℝ} (h₁ : e₁ ≤ e) (h₂ : e ≤ e₂) (c₁ : 3 < e₁) :
    weightMass e ≤ weightMass e₁ + weightMass e₂ := by
  have i₁ := goodLineFiniteLogNorm_exp_integrable e₁ c₁
  have i₂ := goodLineFiniteLogNorm_exp_integrable e₂ (by linarith)
  rw [weightMass, weightMass, weightMass, ← integral_add i₁ i₂]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
  · exact i₁.add i₂
  · exact Filter.Eventually.of_forall (fun _ => exp_mul_le_add h₁ h₂)

theorem weightMass_nonneg (e : ℝ) : 0 ≤ weightMass e :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- On a ball of parameters whose finite exponents stay above `3`, the finite integral is
bounded by one constant times the sup-norm bound. -/
theorem norm_goodLineFiniteVectorIntegral_le_ball (cusp : CuspidalRepresentation) (s₀ : ℂ) (ρ : ℝ)
    (convergent : 3 < (finiteExponent n s₀).re - ρ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound) (bounded : ∀ argument, ‖cusp.realize vector argument‖ ≤ bound)
    (s : ℂ) (hs : s ∈ closedBall s₀ ρ) :
    ‖goodLineFiniteVectorIntegral n cusp s vector‖ ≤
      (weightMass ((finiteExponent n s₀).re - ρ) + weightMass ((finiteExponent n s₀).re + ρ)) * bound := by
  have hre : |s.re - s₀.re| ≤ ρ := by
    calc |s.re - s₀.re| = |(s - s₀).re| := by simp
      _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      _ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.mp hs
  have h₁ : (finiteExponent n s₀).re - ρ ≤ (finiteExponent n s).re := by
    rw [finiteExponent_re, finiteExponent_re]; linarith [(abs_le.mp hre).1]
  have h₂ : (finiteExponent n s).re ≤ (finiteExponent n s₀).re + ρ := by
    rw [finiteExponent_re, finiteExponent_re]; linarith [(abs_le.mp hre).2]
  refine (norm_goodLineFiniteVectorIntegral_le cusp s (by linarith) vector spherical bound bounded).trans ?_
  exact mul_le_mul_of_nonneg_right (weightMass_le h₁ h₂ convergent) bound_nonneg

/-- Analyticity of the finite integral in the standard parameter. -/
theorem goodLineFiniteVectorIntegral_analyticAt' (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) (s : ℂ)
    (convergent : 3 < (finiteExponent n s).re) :
    AnalyticAt ℂ (fun s => goodLineFiniteVectorIntegral n cusp s vector) s :=
  goodLineFiniteVectorIntegral_analyticAt n cusp vector spherical s convergent

/-- Cauchy bound for the parameter derivative of the finite integral. -/
theorem norm_deriv_goodLineFiniteVectorIntegral_le (cusp : CuspidalRepresentation) (s₀ : ℂ) (ρ : ℝ)
    (ρpos : 0 < ρ) (convergent : 3 < (finiteExponent n s₀).re - 2 * ρ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound) (bounded : ∀ argument, ‖cusp.realize vector argument‖ ≤ bound)
    (s : ℂ) (hs : s ∈ closedBall s₀ ρ) :
    ‖deriv (fun s => goodLineFiniteVectorIntegral n cusp s vector) s‖ ≤
      (weightMass ((finiteExponent n s₀).re - 2 * ρ) +
        weightMass ((finiteExponent n s₀).re + 2 * ρ)) * bound / ρ := by
  have hball : closedBall s ρ ⊆ closedBall s₀ (2 * ρ) := by
    intro z hz
    rw [mem_closedBall] at hz hs ⊢
    calc dist z s₀ ≤ dist z s + dist s s₀ := dist_triangle _ _ _
      _ ≤ ρ + ρ := add_le_add hz hs
      _ = 2 * ρ := by ring
  have hconv (z : ℂ) (hz : z ∈ closedBall s₀ (2 * ρ)) : 3 < (finiteExponent n z).re := by
    have hre : |z.re - s₀.re| ≤ 2 * ρ := by
      calc |z.re - s₀.re| = |(z - s₀).re| := by simp
        _ ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
        _ ≤ 2 * ρ := by rw [← dist_eq_norm]; exact mem_closedBall.mp hz
    rw [finiteExponent_re] at convergent ⊢
    linarith [(abs_le.mp hre).1]
  have hdiff : DiffContOnCl ℂ (fun s => goodLineFiniteVectorIntegral n cusp s vector) (ball s ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s ρpos.ne']
    intro z hz
    exact (goodLineFiniteVectorIntegral_analyticAt' cusp vector spherical z
      (hconv z (hball hz))).differentiableAt.differentiableWithinAt
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ρpos hdiff
  intro z hz
  exact norm_goodLineFiniteVectorIntegral_le_ball cusp s₀ (2 * ρ) convergent vector spherical
    bound bound_nonneg bounded z (hball (sphere_subset_closedBall hz))

end TernaryPeriodPolynomials.AnalyticClasses
