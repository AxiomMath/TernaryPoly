module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviFormPullback

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): the core algebraic identities relating `seedTau`,
`seedLinear` at `p` to their values at `leviMap A t p`, and extracting numeric Jacobian entries
from `hasFDerivAt_leviMap`. Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- Component `0,1` of `leviMap`, in reduced form. -/
theorem leviMap_zero (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ) :
    leviMap A t p 0 = (A 0 0 * p 0 + A 0 1 * p 1) / t := by
  unfold leviMap; simp

theorem leviMap_one (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ) :
    leviMap A t p 1 = (A 1 0 * p 0 + A 1 1 * p 1) / t := by
  unfold leviMap; simp

/-- `seedTau` at the Levi-transformed point is the Möbius image of `seedTau p`. -/
theorem seedTau_leviMap (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ) :
    seedTau (leviMap A t p) =
      ((A 0 0 : ℂ) * seedTau p + A 0 1) / ((A 1 0 : ℂ) * seedTau p + A 1 1) := by
  unfold seedTau leviMap
  simp only [Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im _

/-- The Fréchet derivative of `leviMap A t` at `p`, extracted as a numeric function application. -/
theorem leviMap_fderiv_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) (v : Fin 5 → ℝ) (a : Fin 5) :
    fderiv ℝ (leviMap A t) p v a =
      (![(A 0 0 / t) • (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) +
            (A 0 1 / t) • (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ),
          (A 1 0 / t) • (ContinuousLinearMap.proj (0 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) +
            (A 1 1 / t) • (ContinuousLinearMap.proj (1 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ),
          Complex.reCLM.comp
            (((ContinuousLinearMap.toSpanSingleton ℂ
                  ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)).restrictScalars ℝ).comp
              (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
                Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5))))),
          Complex.imCLM.comp
            (((ContinuousLinearMap.toSpanSingleton ℂ
                  ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)).restrictScalars ℝ).comp
              (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 5)) +
                Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 5))))),
          t • (ContinuousLinearMap.proj (4 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)] a) v := by
  rw [(hasFDerivAt_leviMap A t p hden).fderiv]
  rfl

/-- The coefficient substitution `leviCoefficientAction` applies to `seedLinear p` by sending it
to `(δ/d)` times `seedLinear` at the Levi-transformed point, where `δ` is the Möbius denominator
and `d = A.det`. The cross-term cancellation making the `X 2` coefficients match is exactly
`A.det`'s expansion (`Matrix.det_fin_two`). -/
theorem bind_leviCoeffSubst_seedLinear (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hdet : A.det ≠ 0) (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) (ht : t ≠ 0) :
    bind₁ ![C ((A 1 1 / A.det : ℝ) : ℂ) * X 0 + C ((-A 0 1 / A.det : ℝ) : ℂ) * X 1,
        C ((-A 1 0 / A.det : ℝ) : ℂ) * X 0 + C ((A 0 0 / A.det : ℝ) : ℂ) * X 1,
        C ((t⁻¹ : ℝ) : ℂ) * X 2] (seedLinear p) =
      C (((A 1 0 : ℂ) * seedTau p + A 1 1) / (A.det : ℂ)) * seedLinear (leviMap A t p) := by
  have hdetC : (A.det : ℂ) ≠ 0 := by exact_mod_cast hdet
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hdenC' : seedTau p * (A 1 0 : ℂ) + A 1 1 ≠ 0 := by rw [mul_comm]; exact hden
  have hdetval : (A.det : ℂ) = (A 0 0 : ℂ) * A 1 1 - (A 0 1 : ℂ) * A 1 0 := by
    rw [Matrix.det_fin_two]; push_cast; ring
  have hcancel : ((A 1 0 : ℂ) * seedTau p + A 1 1) / A.det *
      (((A 0 0 : ℂ) * seedTau p + A 0 1) / ((A 1 0 : ℂ) * seedTau p + A 1 1)) =
      ((A 0 0 : ℂ) * seedTau p + A 0 1) / A.det := by
    field_simp [hden, hdenC']




  have h0 : (C (seedTau p * (-(A 1 0 : ℂ) / (A.det : ℂ))) : MvPolynomial (Fin 3) ℂ) -
      C ((A 1 1 : ℂ) / (A.det : ℂ)) =
      -(C (((A 1 0 : ℂ) * seedTau p + A 1 1) / (A.det : ℂ))) := by
    rw [← map_neg, ← map_sub]
    congr 1
    ring
  have h1 : (C (seedTau p * ((A 0 0 : ℂ) / (A.det : ℂ))) : MvPolynomial (Fin 3) ℂ) -
      C (-(A 0 1 : ℂ) / (A.det : ℂ)) =
      C ((((A 1 0 : ℂ) * seedTau p + A 1 1) / (A.det : ℂ)) *
        (((A 0 0 : ℂ) * seedTau p + A 0 1) / ((A 1 0 : ℂ) * seedTau p + A 1 1))) := by
    rw [← map_sub, hcancel]
    congr 1
    ring
  have h2 : (C ((p 0 : ℂ)) : MvPolynomial (Fin 3) ℂ) * C ((t : ℂ)⁻¹) -
      C (seedTau p * (p 1 : ℂ)) * C ((t : ℂ)⁻¹) =
      C (((A 1 0 : ℂ) * seedTau p + A 1 1) / (A.det : ℂ) *
          (((A 0 0 : ℂ) * (p 0 : ℂ) + (A 0 1 : ℂ) * (p 1 : ℂ)) / (t : ℂ))) -
      C (((A 1 0 : ℂ) * seedTau p + A 1 1) / (A.det : ℂ) *
          (((A 0 0 : ℂ) * seedTau p + A 0 1) / ((A 1 0 : ℂ) * seedTau p + A 1 1)) *
          (((A 1 0 : ℂ) * (p 0 : ℂ) + (A 1 1 : ℂ) * (p 1 : ℂ)) / (t : ℂ))) := by
    conv_lhs => rw [← sub_mul, ← map_sub, ← C_mul]
    conv_rhs => rw [← map_sub, hcancel]
    congr 1
    field_simp [hdetC, htC]
    rw [hdetval]
    ring
  unfold seedLinear
  rw [seedTau_leviMap, leviMap_zero, leviMap_one]
  -- Phase 1: resolve `bind₁` and distribute multiplication over `seedLinear`'s `+`/`-` structure.
  simp only [map_sub, map_add, map_mul, bind₁_X_right, bind₁_C_right, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_add, mul_sub, sub_mul, ← mul_assoc]



  simp only [← C_mul]
  push_cast
  linear_combination X 0 * h0 + X 1 * h1 + X 2 * h2

end TernaryPeriodPolynomials.Argument
