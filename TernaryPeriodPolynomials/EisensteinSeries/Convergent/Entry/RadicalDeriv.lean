module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointPolynomial

@[expose] public section


/-!
# The derivative of the plane radical along a point power

The radical `planeRadical n χ p Q` depends on `p` only through the unipotent coordinates `(s, t)` and its
coefficients are polynomial in `(s, t)` (`RadicalAnalytic`).  For the binary point power
`Q_z = (X₀ - z X₁)^{n+1}` we compute the real derivative of the coefficients in `(s, t)`:
`d/d(s,t) coeff_m R(s,t) Q_z = -(n+1) (ds - z dt) · coeff_m (X₀ - z X₁ - (s - z t) X₂)^n`
(`hasFDerivAt_radicalCoeff_pointPower`), via the coefficientwise derivative of a polynomial family in one
complex parameter (`hasDerivAt_coeff_pow_sub`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial Polynomial GeneralEisenstein
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- Coefficientwise derivative of a polynomial family in one complex parameter. -/
theorem hasDerivAt_coeff_eval {σ : Type*} (p : Polynomial (MvPolynomial σ ℂ)) (μ : σ →₀ ℕ) (w : ℂ) :
    HasDerivAt (fun x : ℂ => (p.eval (MvPolynomial.C x)).coeff μ)
      (((Polynomial.derivative p).eval (MvPolynomial.C w)).coeff μ) w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.derivative_add]
    exact hp.add hq
  | monomial k a =>
    simp only [Polynomial.eval_monomial, Polynomial.derivative_monomial]
    have e1 : ∀ x : ℂ, (a * MvPolynomial.C x ^ k).coeff μ = a.coeff μ * x ^ k := by
      intro x
      rw [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, mul_comm]
    have e2 : (a * (k : MvPolynomial σ ℂ) * MvPolynomial.C w ^ (k - 1)).coeff μ =
        a.coeff μ * ((k : ℂ) * w ^ (k - 1)) := by
      have : a * (k : MvPolynomial σ ℂ) * MvPolynomial.C w ^ (k - 1) =
          a * MvPolynomial.C ((k : ℂ) * w ^ (k - 1)) := by
        rw [map_mul, map_pow, map_natCast, mul_assoc]
      rw [this, mul_comm, MvPolynomial.coeff_C_mul, mul_comm]
    simp only [e1]
    rw [e2]
    exact (hasDerivAt_pow k w).const_mul _

/-- Derivative of the coefficients of `(B - w · Z)^N` in the complex parameter `w`. -/
theorem hasDerivAt_coeff_pow_sub {σ : Type*} (B Z : MvPolynomial σ ℂ) (N : ℕ) (μ : σ →₀ ℕ) (w : ℂ) :
    HasDerivAt (fun x : ℂ => ((B - MvPolynomial.C x * Z) ^ N).coeff μ)
      ((-(N : MvPolynomial σ ℂ) * Z * (B - MvPolynomial.C w * Z) ^ (N - 1)).coeff μ) w := by
  have h := hasDerivAt_coeff_eval ((Polynomial.C B - Polynomial.X * Polynomial.C Z) ^ N) μ w
  have e1 : ∀ x : ℂ, ((Polynomial.C B - Polynomial.X * Polynomial.C Z) ^ N).eval (MvPolynomial.C x) =
      (B - MvPolynomial.C x * Z) ^ N := by
    intro x
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, mul_comm (MvPolynomial.C x)]
  have e2 : ((Polynomial.derivative ((Polynomial.C B - Polynomial.X * Polynomial.C Z) ^ N)).eval
      (MvPolynomial.C w)) = -(N : MvPolynomial σ ℂ) * Z * (B - MvPolynomial.C w * Z) ^ (N - 1) := by
    rw [Polynomial.derivative_pow]
    simp [Polynomial.eval_pow]
    ring
  simp only [e1, e2] at h
  exact h

/-- The binary point power `(X₀ - z X₁)^N`, embedded in the ternary polynomials. -/
def pointPowerTernary (z : ℂ) : Poly := (MvPolynomial.X 0 - MvPolynomial.C z * MvPolynomial.X 1 : Poly)

theorem binaryEmbed_pointPower (N : ℕ) (z : ℂ) :
    binaryEmbed N (binaryPointPower N z) = pointPowerTernary z ^ N := by
  rw [binaryEmbed_apply]
  simp [binaryPointPower, pointPowerTernary]

theorem planeUnipotent_inv_val (s t : ℂ) :
    (((GeneralEisenstein.Adelic.planeUnipotent s t)⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) =
      !![1, 0, -s; 0, 1, -t; 0, 0, 1] := rfl

theorem unipSubst_pointPower (N : ℕ) (z : ℂ) (st : ℝ × ℝ) :
    unipSubst st (pointPowerTernary z ^ N) =
      (pointPowerTernary z - MvPolynomial.C ((st.1 : ℂ) - z * (st.2 : ℂ)) * MvPolynomial.X 2) ^ N := by
  have hX0 : unipSubst st (MvPolynomial.X 0) = MvPolynomial.X 0 - MvPolynomial.C (st.1 : ℂ) * MvPolynomial.X 2 := by
    unfold unipSubst
    rw [substitute_X, linearForm, Fin.sum_univ_three]
    have e0 : (((GeneralEisenstein.Adelic.planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ) 0 0 = 1 := rfl
    have e1 : (((GeneralEisenstein.Adelic.planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ) 0 1 = 0 := rfl
    have e2 : (((GeneralEisenstein.Adelic.planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ) 0 2 = -(algebraMap ℝ ℂ st.1) := rfl
    rw [e0, e1, e2]
    simp [sub_eq_add_neg, Complex.coe_algebraMap]
  have hX1 : unipSubst st (MvPolynomial.X 1) = MvPolynomial.X 1 - MvPolynomial.C (st.2 : ℂ) * MvPolynomial.X 2 := by
    unfold unipSubst
    rw [substitute_X, linearForm, Fin.sum_univ_three]
    have e0 : (((GeneralEisenstein.Adelic.planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ) 1 0 = 0 := rfl
    have e1 : (((GeneralEisenstein.Adelic.planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ) 1 1 = 1 := rfl
    have e2 : (((GeneralEisenstein.Adelic.planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ) 1 2 = -(algebraMap ℝ ℂ st.2) := rfl
    rw [e0, e1, e2]
    simp [sub_eq_add_neg, Complex.coe_algebraMap]
  rw [map_pow]
  congr 1
  have hC : unipSubst st (MvPolynomial.C z) = MvPolynomial.C z := MvPolynomial.algHom_C _ z
  unfold pointPowerTernary
  rw [map_sub, map_mul, hC, hX0, hX1]
  simp only [map_sub, map_mul]
  ring

/-- The real-linear map `(ds, dt) ↦ c (ds - z dt)`. -/
def radLin (c z : ℂ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight c + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-(c * z))

@[simp] theorem radLin_apply (c z : ℂ) (v : ℝ × ℝ) : radLin c z v = c * ((v.1 : ℂ) - z * (v.2 : ℂ)) := by
  simp only [radLin, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [Complex.real_smul, Complex.real_smul]
  ring

theorem coeff_X2_mul' (R : Poly) (m : Fin 3 →₀ ℕ) :
    ((MvPolynomial.X 2 : Poly) * R).coeff (m + Finsupp.single 2 1) = R.coeff m :=
  coeff_X2_mul R m

/-- **The derivative of the radical coefficients on a point power.** -/
theorem hasFDerivAt_radicalCoeff_pointPower (n : ℕ) (z : ℂ) (m : Fin 3 →₀ ℕ) (st : ℝ × ℝ) :
    HasFDerivAt (radicalCoeff n (binaryPointPower (n + 1) z) m)
      (radLin (-((n + 1 : ℕ) : ℂ) * ((pointPowerTernary z -
        MvPolynomial.C ((st.1 : ℂ) - z * (st.2 : ℂ)) * MvPolynomial.X 2) ^ n).coeff m) z) st := by
  set w : ℝ × ℝ → ℂ := fun v => (v.1 : ℂ) - z * (v.2 : ℂ) with hw
  have hwL : w = radLin 1 z := by
    funext v
    simp [hw]
  have hLw : HasFDerivAt w (radLin 1 z) st := by
    rw [hwL]
    exact (radLin 1 z).hasFDerivAt
  have hg := hasDerivAt_coeff_pow_sub (pointPowerTernary z) (MvPolynomial.X 2) (n + 1)
    (m + Finsupp.single 2 1) (w st)
  have hcomp := ((hg.hasFDerivAt.restrictScalars ℝ).comp st hLw).sub_const
    ((binaryEmbed (n + 1) (binaryPointPower (n + 1) z)).coeff (m + Finsupp.single 2 1))
  have hfun : radicalCoeff n (binaryPointPower (n + 1) z) m = fun v =>
      ((pointPowerTernary z - MvPolynomial.C (w v) * MvPolynomial.X 2) ^ (n + 1)).coeff
        (m + Finsupp.single 2 1) - (binaryEmbed (n + 1) (binaryPointPower (n + 1) z)).coeff
          (m + Finsupp.single 2 1) := by
    funext v
    rw [radicalCoeff, MvPolynomial.coeff_sub, binaryEmbed_pointPower, unipSubst_pointPower]
  have hD : ((-(((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ)) * MvPolynomial.X 2 *
      (pointPowerTernary z - MvPolynomial.C (w st) * MvPolynomial.X 2) ^ (n + 1 - 1))).coeff
        (m + Finsupp.single 2 1) =
      -((n + 1 : ℕ) : ℂ) * ((pointPowerTernary z -
        MvPolynomial.C ((st.1 : ℂ) - z * (st.2 : ℂ)) * MvPolynomial.X 2) ^ n).coeff m := by
    have e : (-(((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ)) * MvPolynomial.X 2 *
        (pointPowerTernary z - MvPolynomial.C (w st) * MvPolynomial.X 2) ^ (n + 1 - 1)) =
        MvPolynomial.X 2 * (MvPolynomial.C (-((n + 1 : ℕ) : ℂ)) *
          (pointPowerTernary z - MvPolynomial.C (w st) * MvPolynomial.X 2) ^ n) := by
      rw [map_neg, map_natCast, Nat.add_sub_cancel]
      ring
    rw [e, coeff_X2_mul', MvPolynomial.coeff_C_mul]
  rw [hfun]
  refine hcomp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, radLin_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, one_mul, smul_eq_mul, hD]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
