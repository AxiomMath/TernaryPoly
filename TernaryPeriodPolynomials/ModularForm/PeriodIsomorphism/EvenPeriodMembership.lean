module

public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodAxis
public import TernaryPeriodPolynomials.ModularForm.Periods.PeriodHomogeneous

@[expose] public section


/-!
# General even-period membership (Corollary 1.4 plan step (i))

Generalizes
`TernaryPeriodPolynomials.Argument.CuspForms.EvenPeriodRelations`'s degree-ten-specific
`normalizedEvenPeriodPart_mem_evenPeriodSpace_ten` to every nonzero even `n`, using the
already-general eval-level identities of `EvenPeriodEval.lean`/`EvenPeriodAxis.lean` and the
already-general homogeneity fact `normalizedEvenPeriodPart_isHomogeneous` of
`PeriodHomogeneous.lean`. Every step below mirrors the degree-ten proof verbatim, with
`n`/`hn`/`hn0` replacing `10`/`even_ten`/the implicit `10 ≠ 0`.
-/

noncomputable section
open Complex MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPoly.BinaryCuspPeriod TernaryPeriodPolynomials.Argument.CuspForms

/-- Eval-level unfolding of `normalizedEvenPeriodPart n` in terms of `evenPeriod`. -/
theorem eval_normalizedEvenPeriodPart {n : ℕ} (hn : Even n) (f : Forms n) (x y : ℂ) :
    eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) =
      eval (![x, y] : Fin 2 → ℂ) (evenPeriod f) - periodCoefficient f n * (x ^ n - y ^ n) := by
  have hc : eval (![1, 0] : Fin 2 → ℂ)
      (TernaryPeriodPolynomials.Argument.evenPeriodPart n f) = periodCoefficient f n := by
    rw [← evenPeriod_eq_evenPeriodPart, eval_evenPeriod_axis_last hn f 1, one_pow, mul_one]
  rw [TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart, map_sub, map_mul, eval_C, hc,
    ← evenPeriod_eq_evenPeriodPart]
  simp only [map_sub, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem eval_normalizedEvenPeriodPart_axis_zero {n : ℕ} (hn0 : n ≠ 0) (hn : Even n)
    (f : Forms n) (y : ℂ) :
    eval (![0, y] : Fin 2 → ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) = 0 := by
  rw [eval_normalizedEvenPeriodPart hn, eval_evenPeriod_axis_zero, zero_pow hn0]
  linear_combination y ^ n * periodCoefficient_boundary hn f

theorem eval_normalizedEvenPeriodPart_axis_last {n : ℕ} (hn0 : n ≠ 0) (hn : Even n)
    (f : Forms n) (x : ℂ) :
    eval (![x, 0] : Fin 2 → ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) = 0 := by
  rw [eval_normalizedEvenPeriodPart hn, eval_evenPeriod_axis_last hn, zero_pow hn0]
  ring

theorem eval_normalizedEvenPeriodPart_S {n : ℕ} (hn : Even n) (f : Forms n) (x y : ℂ) :
    eval (![-y, x] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) =
      - eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) := by
  rw [eval_normalizedEvenPeriodPart hn, eval_normalizedEvenPeriodPart hn, eval_evenPeriod_S hn,
    hn.neg_pow]
  ring

theorem eval_normalizedEvenPeriodPart_threeTerm {n : ℕ} (hn : Even n) (f : Forms n) (x y : ℂ) :
    eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) +
      eval (![-y, x - y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) +
      eval (![y - x, -x] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) = 0 := by
  have h1 := eval_normalizedEvenPeriodPart hn f x y
  have h2 := eval_normalizedEvenPeriodPart hn f (-y) (x - y)
  have h3 := eval_normalizedEvenPeriodPart hn f (y - x) (-x)
  have hE := eval_evenPeriod_threeTerm hn f x y
  have hEy : ((-y : ℂ)) ^ n = y ^ n := hn.neg_pow y
  have hEx : ((-x : ℂ)) ^ n = x ^ n := hn.neg_pow x
  have hSwap : (y - x : ℂ) ^ n = (x - y) ^ n := by
    rw [show (y - x : ℂ) = -(x - y) by ring, hn.neg_pow]
  linear_combination h1 + h2 + h3 + hE - periodCoefficient f n * hEy +
    periodCoefficient f n * hEx - periodCoefficient f n * hSwap

theorem eval_normalizedEvenPeriodPart_even_first {n : ℕ} (hn : Even n) (f : Forms n) (x y : ℂ) :
    eval (![-x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) =
      eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) := by
  rw [eval_normalizedEvenPeriodPart hn, eval_normalizedEvenPeriodPart hn,
    eval_evenPeriod_even_first, hn.neg_pow]

theorem normalizedEvenPeriodPart_axis_first {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) (f : Forms n) :
    bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) = 0 := by
  apply MvPolynomial.funext
  intro v
  rw [eval_bind_binary]
  simp only [map_zero, eval_X]
  exact eval_normalizedEvenPeriodPart_axis_zero hn0 hn f (v 1)

theorem normalizedEvenPeriodPart_axis_second {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) (f : Forms n) :
    bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) = 0 := by
  apply MvPolynomial.funext
  intro v
  rw [eval_bind_binary]
  simp only [map_zero, eval_X]
  exact eval_normalizedEvenPeriodPart_axis_last hn0 hn f (v 0)

theorem normalizedEvenPeriodPart_two_term {n : ℕ} (hn : Even n) (f : Forms n) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f +
      bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) = 0 := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, map_add, eval_bind_binary, map_zero]
  simp only [map_neg, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eval_normalizedEvenPeriodPart_S hn f (v 0) (v 1)]
  ring

theorem normalizedEvenPeriodPart_three_term {n : ℕ} (hn : Even n) (f : Forms n) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) = 0 := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, map_add, map_add, eval_bind_binary, eval_bind_binary, map_zero]
  simp only [map_sub, map_neg, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact eval_normalizedEvenPeriodPart_threeTerm hn f (v 0) (v 1)

theorem normalizedEvenPeriodPart_kernel {n : ℕ} (hn : Even n) (f : Forms n) :
    bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) -
      TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f = 0 := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, map_sub, eval_bind_binary, map_zero]
  simp only [map_neg, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eval_normalizedEvenPeriodPart_even_first hn f (v 0) (v 1)]
  ring

theorem normalizedEvenPeriodPart_periodRelations {n : ℕ} (hn0 : n ≠ 0) (hn : Even n)
    (f : Forms n) :
    TernaryPoly.Paper.PeriodRelations
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) :=
  ⟨normalizedEvenPeriodPart_axis_first hn0 hn f, normalizedEvenPeriodPart_axis_second hn0 hn f,
    normalizedEvenPeriodPart_two_term hn f, normalizedEvenPeriodPart_three_term hn f⟩

/-- **Plan step (i).** For every nonzero even `n`, `normalizedEvenPeriodPart n h` lies in
`evenPeriodSpace ℂ n`, for every level-one cusp form `h` of weight `n + 2`. -/
theorem normalizedEvenPeriodPart_mem_evenPeriodSpace {n : ℕ} (hn0 : n ≠ 0) (hn : Even n)
    (f : Forms n) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f ∈
      TernaryPoly.Paper.evenPeriodSpace ℂ n := by
  refine ⟨⟨normalizedEvenPeriodPart_isHomogeneous f,
    normalizedEvenPeriodPart_periodRelations hn0 hn f⟩, ?_⟩
  show bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) -
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f = 0
  exact normalizedEvenPeriodPart_kernel hn f

end TernaryPeriodPolynomials.Argument.Corollary14
