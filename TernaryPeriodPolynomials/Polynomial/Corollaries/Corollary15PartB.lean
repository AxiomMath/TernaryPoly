module

public import TernaryPeriodPolynomials.Polynomial.Corollaries.AlternatingTenPeriodRelations
public import TernaryPeriodPolynomials.Polynomial.Corollaries.CancelLinearFactor
public import TernaryPeriodPolynomials.Polynomial.Corollaries.PositiveCharacteristic
public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Restriction

@[expose] public section


/-! Corollary 1.5, part (b): any `g` dividing every solution must itself divide
`universalDivisor F`, i.e. `universalDivisor F` is (up to units) the GCD of all solutions.

"Prime peeling" strategy, using only the project's own substitution-based divisibility toolkit
(`CancelLinearFactor.lean`), with no abstract UFD/`Prime` machinery:
* Instantiate the hypothesis at `symmetricTenSolution F` and `alternatingTenSolution F`.
* `alternatingTenSolution F` factors as `universalDivisor F` times six extra linear forms
  (`alternatingTenSolution_factor`), so `g` divides this product.
* `symmetricTenSolution F` is nonzero at a root of each of the six extra linear forms, so none of
  them divides `symmetricTenSolution F`; since `g` divides it too, none of them divides `g`
  either (`dvd_trans` contrapositive).
* Peel the six extra factors off one at a time with `dvd_of_dvd_mul_linear_of_not_dvd`, landing
  on `g ∣ universalDivisor F`. -/


open MvPolynomial TernaryPoly TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- `alternatingTenSolution` factors as `universalDivisor` times six extra linear forms, each
pre-written in `X i - c` shape for direct use with `dvd_of_dvd_mul_linear_of_not_dvd`. -/
theorem alternatingTenSolution_factor :
    alternatingTenSolution F = universalDivisor F * (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 0) *
      (X 0 - (X 2 - X 1)) * (X 1 - (X 0 - X 2)) * (X 2 - (X 1 - X 0)) := by
  simp only [alternatingTenSolution, cyclicLift, binaryEval, alternatingTenPeriod,
    universalDivisor, map_mul, map_sub, map_pow, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem p1_ne : (X 0 - X 1 : Ternary F) ≠ 0 := by
  intro h; have := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → F)) h; simp at this

private theorem p2_ne : (X 1 - X 2 : Ternary F) ≠ 0 := by
  intro h; have := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → F)) h; simp at this

private theorem p3_ne : (X 2 - X 0 : Ternary F) ≠ 0 := by
  intro h; have := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → F)) h; simp at this

private theorem p4_ne : (X 0 - (X 2 - X 1) : Ternary F) ≠ 0 := by
  intro h; have := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → F)) h; simp at this

private theorem p5_ne : (X 1 - (X 0 - X 2) : Ternary F) ≠ 0 := by
  intro h; have := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → F)) h; simp at this

private theorem p6_ne : (X 2 - (X 1 - X 0) : Ternary F) ≠ 0 := by
  intro h; have := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → F)) h; simp at this

private theorem symmetricTenSolution_eval_p1_root :
    MvPolynomial.eval (![3, 3, 1] : Fin 3 → F) (symmetricTenSolution F) ≠ 0 := by
  simp [symmetricTenSolution, cyclicLift, binaryEval, symmetricTenPeriod,
    map_mul, map_sub, map_pow, map_add, map_ofNat, bind₁_X_right]
  norm_num

private theorem symmetricTenSolution_eval_p2_root :
    MvPolynomial.eval (![1, 3, 3] : Fin 3 → F) (symmetricTenSolution F) ≠ 0 := by
  simp [symmetricTenSolution, cyclicLift, binaryEval, symmetricTenPeriod,
    map_mul, map_sub, map_pow, map_add, map_ofNat, bind₁_X_right]
  norm_num

private theorem symmetricTenSolution_eval_p3_root :
    MvPolynomial.eval (![3, 1, 3] : Fin 3 → F) (symmetricTenSolution F) ≠ 0 := by
  simp [symmetricTenSolution, cyclicLift, binaryEval, symmetricTenPeriod,
    map_mul, map_sub, map_pow, map_add, map_ofNat, bind₁_X_right]
  norm_num

private theorem symmetricTenSolution_eval_p4_root :
    MvPolynomial.eval (![1, 3, 4] : Fin 3 → F) (symmetricTenSolution F) ≠ 0 := by
  simp [symmetricTenSolution, cyclicLift, binaryEval, symmetricTenPeriod,
    map_mul, map_sub, map_pow, map_add, map_ofNat, bind₁_X_right]
  norm_num

private theorem symmetricTenSolution_eval_p5_root :
    MvPolynomial.eval (![4, 1, 3] : Fin 3 → F) (symmetricTenSolution F) ≠ 0 := by
  simp [symmetricTenSolution, cyclicLift, binaryEval, symmetricTenPeriod,
    map_mul, map_sub, map_pow, map_add, map_ofNat, bind₁_X_right]
  norm_num

private theorem symmetricTenSolution_eval_p6_root :
    MvPolynomial.eval (![3, 4, 1] : Fin 3 → F) (symmetricTenSolution F) ≠ 0 := by
  simp [symmetricTenSolution, cyclicLift, binaryEval, symmetricTenPeriod,
    map_mul, map_sub, map_pow, map_add, map_ofNat, bind₁_X_right]
  norm_num

omit [CharZero F] in
/-- If `p ∣ q` and `p` vanishes at `v`, so does `q`. -/
private theorem eval_eq_zero_of_dvd {p q : Ternary F} {v : Fin 3 → F} (hpd : p ∣ q)
    (hp0 : MvPolynomial.eval v p = 0) : MvPolynomial.eval v q = 0 := by
  obtain ⟨k, hk⟩ := hpd
  rw [hk, map_mul, hp0, zero_mul]

/-- Corollary 1.5, part (b): any common divisor `g` of all solutions divides `universalDivisor`.
-/
theorem universalDivisor_dvd_of_universal_property {g : Ternary F}
    (hg : ∀ f, Solution f → g ∣ f) : g ∣ universalDivisor F := by
  have hg_fs : g ∣ symmetricTenSolution F := hg _ (symmetricTenSolution_solution F)
  have hg_fa : g ∣ alternatingTenSolution F := hg _ (alternatingTenSolution_solution F)
  rw [alternatingTenSolution_factor] at hg_fa
  have hnd1 : ¬ (X 0 - X 1 : Ternary F) ∣ g := by
    intro hpd
    have hroot : MvPolynomial.eval (![3, 3, 1] : Fin 3 → F) (X 0 - X 1 : Ternary F) = 0 := by
      simp
    exact symmetricTenSolution_eval_p1_root (eval_eq_zero_of_dvd (dvd_trans hpd hg_fs) hroot)
  have hnd2 : ¬ (X 1 - X 2 : Ternary F) ∣ g := by
    intro hpd
    have hroot : MvPolynomial.eval (![1, 3, 3] : Fin 3 → F) (X 1 - X 2 : Ternary F) = 0 := by
      simp
    exact symmetricTenSolution_eval_p2_root (eval_eq_zero_of_dvd (dvd_trans hpd hg_fs) hroot)
  have hnd3 : ¬ (X 2 - X 0 : Ternary F) ∣ g := by
    intro hpd
    have hroot : MvPolynomial.eval (![3, 1, 3] : Fin 3 → F) (X 2 - X 0 : Ternary F) = 0 := by
      simp
    exact symmetricTenSolution_eval_p3_root (eval_eq_zero_of_dvd (dvd_trans hpd hg_fs) hroot)
  have hnd4 : ¬ (X 0 - (X 2 - X 1) : Ternary F) ∣ g := by
    intro hpd
    have hroot : MvPolynomial.eval (![1, 3, 4] : Fin 3 → F)
        (X 0 - (X 2 - X 1) : Ternary F) = 0 := by simp; norm_num
    exact symmetricTenSolution_eval_p4_root (eval_eq_zero_of_dvd (dvd_trans hpd hg_fs) hroot)
  have hnd5 : ¬ (X 1 - (X 0 - X 2) : Ternary F) ∣ g := by
    intro hpd
    have hroot : MvPolynomial.eval (![4, 1, 3] : Fin 3 → F)
        (X 1 - (X 0 - X 2) : Ternary F) = 0 := by simp; norm_num
    exact symmetricTenSolution_eval_p5_root (eval_eq_zero_of_dvd (dvd_trans hpd hg_fs) hroot)
  have hnd6 : ¬ (X 2 - (X 1 - X 0) : Ternary F) ∣ g := by
    intro hpd
    have hroot : MvPolynomial.eval (![3, 4, 1] : Fin 3 → F)
        (X 2 - (X 1 - X 0) : Ternary F) = 0 := by simp; norm_num
    exact symmetricTenSolution_eval_p6_root (eval_eq_zero_of_dvd (dvd_trans hpd hg_fs) hroot)
  have hself6 : bind₁ (Function.update X 2 (X 1 - X 0) : Fin 3 → Ternary F)
      (X 2 - (X 1 - X 0)) = 0 := by simp
  have step6 : g ∣ universalDivisor F * (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 0) *
      (X 0 - (X 2 - X 1)) * (X 1 - (X 0 - X 2)) :=
    dvd_of_dvd_mul_linear_of_not_dvd hself6 p6_ne hg_fa hnd6
  have hself5 : bind₁ (Function.update X 1 (X 0 - X 2) : Fin 3 → Ternary F)
      (X 1 - (X 0 - X 2)) = 0 := by simp
  have step5 : g ∣ universalDivisor F * (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 0) *
      (X 0 - (X 2 - X 1)) :=
    dvd_of_dvd_mul_linear_of_not_dvd hself5 p5_ne step6 hnd5
  have hself4 : bind₁ (Function.update X 0 (X 2 - X 1) : Fin 3 → Ternary F)
      (X 0 - (X 2 - X 1)) = 0 := by simp
  have step4 : g ∣ universalDivisor F * (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 0) :=
    dvd_of_dvd_mul_linear_of_not_dvd hself4 p4_ne step5 hnd4
  have hself3 : bind₁ (Function.update X 2 (X 0) : Fin 3 → Ternary F) (X 2 - X 0) = 0 := by
    simp
  have step3 : g ∣ universalDivisor F * (X 0 - X 1) * (X 1 - X 2) :=
    dvd_of_dvd_mul_linear_of_not_dvd hself3 p3_ne step4 hnd3
  have hself2 : bind₁ (Function.update X 1 (X 2) : Fin 3 → Ternary F) (X 1 - X 2) = 0 := by
    simp
  have step2 : g ∣ universalDivisor F * (X 0 - X 1) :=
    dvd_of_dvd_mul_linear_of_not_dvd hself2 p2_ne step3 hnd2
  have hself1 : bind₁ (Function.update X 0 (X 1) : Fin 3 → Ternary F) (X 0 - X 1) = 0 := by
    simp
  exact dvd_of_dvd_mul_linear_of_not_dvd hself1 p1_ne step2 hnd1

end TernaryPeriodPolynomials.Argument
