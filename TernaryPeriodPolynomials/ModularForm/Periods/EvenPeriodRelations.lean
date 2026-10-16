module

public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodNonvanishing
public import TernaryPeriodPolynomials.ModularForm.Periods.PeriodHomogeneous
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenLinearIndependence

@[expose] public section



/-!
# `normalizedEvenPeriodPart 10 h` satisfies the period relations and lies in `evenPeriodSpace`

The even-side counterpart of `oddPeriod_mem_space`/`oddPeriodPart_mem_oddPeriodSpace`
(`ExampleDegreeTenCuspBridge.lean`), for which no `evenPeriodSpace`/`BinaryComplexPeriod`-style
shortcut bridge exists: membership is built directly from `PeriodRelations` plus the kernel
condition of `bind₁ ![-X 0, X 1]`. The key input is the eval-level unfolding
`eval_normalizedEvenPeriodPart_ten`, expressing `normalizedEvenPeriodPart 10 f` pointwise as
`evenPeriod f` minus the axis correction `periodCoefficient f 10 * (x ^ 10 - y ^ 10)`; combined
with the eval-level even-period identities of `EvenPeriodEval.lean`/`EvenPeriodAxis.lean`, each
`PeriodRelations` clause reduces either to a pure `ring` identity (the two-term, three-term, axis
second and kernel clauses, using that `10` is even so `ring` normalizes `(-t) ^ 10` to `t ^ 10`)
or to a one-line `linear_combination` against `periodCoefficient_boundary` (the axis-first
clause, which needs the external fact `periodCoefficient f 10 = -periodCoefficient f 0`).
Combined with the nonvanishing of `EvenPeriodNonvanishing.lean`, this gives `conjunct2_even`, the
even/alternating half of `example_degree_ten`'s second conjunct, mirroring `conjunct2_odd`.
-/

noncomputable section
open Complex MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CuspForms

open TernaryPoly.BinaryCuspPeriod

/-- Eval-level unfolding of `normalizedEvenPeriodPart 10` in terms of `evenPeriod`. -/
theorem eval_normalizedEvenPeriodPart_ten (f : Forms 10) (x y : ℂ) :
    eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) =
      eval (![x, y] : Fin 2 → ℂ) (evenPeriod f) - periodCoefficient f 10 * (x ^ 10 - y ^ 10) := by
  have hc : eval (![1, 0] : Fin 2 → ℂ)
      (TernaryPeriodPolynomials.Argument.evenPeriodPart 10 f) = periodCoefficient f 10 := by
    rw [← evenPeriod_eq_evenPeriodPart, eval_evenPeriod_axis_last even_ten f 1, one_pow, mul_one]
  rw [TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart, map_sub, map_mul, eval_C, hc,
    ← evenPeriod_eq_evenPeriodPart]
  simp only [map_sub, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem eval_normalizedEvenPeriodPart_axis_zero (f : Forms 10) (y : ℂ) :
    eval (![0, y] : Fin 2 → ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) = 0 := by
  rw [eval_normalizedEvenPeriodPart_ten, eval_evenPeriod_axis_zero,
    show (0 : ℂ) ^ 10 = 0 by norm_num]
  linear_combination y ^ 10 * periodCoefficient_boundary even_ten f

theorem eval_normalizedEvenPeriodPart_axis_last (f : Forms 10) (x : ℂ) :
    eval (![x, 0] : Fin 2 → ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) = 0 := by
  rw [eval_normalizedEvenPeriodPart_ten, eval_evenPeriod_axis_last even_ten,
    show (0 : ℂ) ^ 10 = 0 by norm_num]
  ring

theorem eval_normalizedEvenPeriodPart_S (f : Forms 10) (x y : ℂ) :
    eval (![-y, x] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) =
      - eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) := by
  rw [eval_normalizedEvenPeriodPart_ten, eval_normalizedEvenPeriodPart_ten,
    eval_evenPeriod_S even_ten]
  ring

theorem eval_normalizedEvenPeriodPart_threeTerm (f : Forms 10) (x y : ℂ) :
    eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) +
      eval (![-y, x - y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) +
      eval (![y - x, -x] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) = 0 := by
  have h1 := eval_normalizedEvenPeriodPart_ten f x y
  have h2 := eval_normalizedEvenPeriodPart_ten f (-y) (x - y)
  have h3 := eval_normalizedEvenPeriodPart_ten f (y - x) (-x)
  have hE := eval_evenPeriod_threeTerm even_ten f x y
  linear_combination h1 + h2 + h3 + hE

theorem eval_normalizedEvenPeriodPart_even_first (f : Forms 10) (x y : ℂ) :
    eval (![-x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) =
      eval (![x, y] : Fin 2 → ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) := by
  rw [eval_normalizedEvenPeriodPart_ten, eval_normalizedEvenPeriodPart_ten,
    eval_evenPeriod_even_first]
  ring

theorem normalizedEvenPeriodPart_axis_first (f : Forms 10) :
    bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) = 0 := by
  apply MvPolynomial.funext
  intro v
  rw [eval_bind_binary]
  simp only [map_zero, eval_X]
  exact eval_normalizedEvenPeriodPart_axis_zero f (v 1)

theorem normalizedEvenPeriodPart_axis_second (f : Forms 10) :
    bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) = 0 := by
  apply MvPolynomial.funext
  intro v
  rw [eval_bind_binary]
  simp only [map_zero, eval_X]
  exact eval_normalizedEvenPeriodPart_axis_last f (v 0)

theorem normalizedEvenPeriodPart_two_term (f : Forms 10) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f +
      bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) = 0 := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, map_add, eval_bind_binary, map_zero]
  simp only [map_neg, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eval_normalizedEvenPeriodPart_S f (v 0) (v 1)]
  ring

theorem normalizedEvenPeriodPart_three_term (f : Forms 10) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) = 0 := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, map_add, map_add, eval_bind_binary, eval_bind_binary, map_zero]
  simp only [map_sub, map_neg, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact eval_normalizedEvenPeriodPart_threeTerm f (v 0) (v 1)

theorem normalizedEvenPeriodPart_kernel (f : Forms 10) :
    bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
        (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) -
      TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f = 0 := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, map_sub, eval_bind_binary, map_zero]
  simp only [map_neg, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eval_normalizedEvenPeriodPart_even_first f (v 0) (v 1)]
  ring

theorem normalizedEvenPeriodPart_periodRelations (f : Forms 10) :
    TernaryPoly.Paper.PeriodRelations
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) :=
  ⟨normalizedEvenPeriodPart_axis_first f, normalizedEvenPeriodPart_axis_second f,
    normalizedEvenPeriodPart_two_term f, normalizedEvenPeriodPart_three_term f⟩

theorem normalizedEvenPeriodPart_mem_evenPeriodSpace_ten (f : Forms 10) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f ∈
      TernaryPoly.Paper.evenPeriodSpace ℂ 10 := by
  refine ⟨⟨normalizedEvenPeriodPart_isHomogeneous f, normalizedEvenPeriodPart_periodRelations f⟩,
    ?_⟩
  show bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ)
      (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f) -
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 f = 0
  exact normalizedEvenPeriodPart_kernel f

/-- For a nonzero weight-twelve level-one cusp form `h`, `normalizedEvenPeriodPart 10 h` lies in
`evenPeriodSpace ℂ 10` and is nonzero. The even-side analogue of `oddPeriodPart_mem_and_ne_zero`. -/
theorem normalizedEvenPeriodPart_mem_and_ne_zero {h : CuspForm levelOne 12} (hh0 : h ≠ 0) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 h ∈
        TernaryPoly.Paper.evenPeriodSpace ℂ 10 ∧
      TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 h ≠ 0 :=
  ⟨normalizedEvenPeriodPart_mem_evenPeriodSpace_ten h,
    normalizedEvenPeriodPart_ne_zero_of_ne_zero_ten hh0⟩

/-- **Conjunct 2, even/alternating half of `example_degree_ten`.** For every nonzero
weight-twelve level-one cusp form `h`, `alternatingTenPeriod ℂ` is a nonzero scalar multiple of
`normalizedEvenPeriodPart 10 h`. -/
theorem conjunct2_even {h : CuspForm levelOne 12} (hh0 : h ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ alternatingTenPeriod ℂ =
      c • TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 h := by
  obtain ⟨hmem, hne⟩ := normalizedEvenPeriodPart_mem_and_ne_zero hh0
  set S := TernaryPoly.Paper.evenPeriodSpace ℂ 10
  have hdim : Module.finrank ℂ S = 1 := evenPeriodSpace_ten_finrank_eq_one ℂ
  have hsmem : alternatingTenPeriod ℂ ∈ S := alternatingTenPeriod_mem_evenPeriodSpace
  set v : S := ⟨TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart 10 h, hmem⟩ with hv_def
  set w : S := ⟨alternatingTenPeriod ℂ, hsmem⟩ with hw_def
  have hv0 : v ≠ 0 := fun hcontra => hne (congrArg Subtype.val hcontra)
  have hspan : (ℂ ∙ v) = ⊤ := (finrank_eq_one_iff_of_nonzero v hv0).mp hdim
  have hwmem : w ∈ ℂ ∙ v := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwmem
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    rw [hc0, zero_smul] at hc
    exact alternatingTenPeriod_ne_zero' ℂ (congrArg Subtype.val hc.symm)
  · have hc' : (c • v : S).val = w.val := congrArg Subtype.val hc
    rw [Submodule.coe_smul] at hc'
    exact hc'.symm

end TernaryPeriodPolynomials.Argument.CuspForms
