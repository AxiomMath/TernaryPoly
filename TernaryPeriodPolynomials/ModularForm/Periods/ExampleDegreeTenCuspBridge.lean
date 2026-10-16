module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Period.Axis
public import TernaryPeriodPolynomials.ModularForm.Period.Basic
public import TernaryPeriodPolynomials.ModularForm.Period.Injective
public import TernaryPeriodPolynomials.Polynomial.Classification
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenDimension
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenAlgebra

@[expose] public section


/-!
# Degree-ten cusp-form bridge (partial progress toward `example_degree_ten`)

This file bridges the `TernaryPoly.BinaryCuspPeriod` period-polynomial machinery (defined via
moments of cusp forms) to the `TernaryPeriodPolynomials.Argument.oddPeriodPart`
definition, specialized to weight twelve / degree ten, where `Forms 10` is one-dimensional
(`Module.finrank ℂ (Forms 10) = 1`). One-dimensionality trivializes Hecke-kernel stability,
giving an unconditional proof that the (unconditional) odd period map is injective on `Forms 10`,
and from there that `symmetricTenPeriod ℂ` is a nonzero scalar multiple of `oddPeriodPart 10 h`
for every nonzero weight-twelve level-one cusp form `h` (`conjunct2_odd` below).

This file closes only the odd/symmetric half of `example_degree_ten`'s second conjunct
(`conjunct2_odd`). The even/alternating half is the analogous statement for
`alternatingTenPeriod` against `normalizedEvenPeriodPart`; it needed genuinely different
infrastructure (`PeriodRelations`/kernel-condition membership in `evenPeriodSpace`, built
directly rather than via a `BinaryComplexPeriod`-style bridge, plus a separate Euler-product
nonvanishing argument) and is proved in `EvenPeriodRelations.lean`/`EvenPeriodNonvanishing.lean`
(`conjunct2_even`). See `ExampleDegreeTenAssembly.lean` for the final assembly of both halves into
`example_degree_ten`.
-/


open TernaryPoly.BinaryCuspPeriod TernaryPoly.BinaryCuspPeriodInjective MvPolynomial
  TernaryPeriodPolynomials.Argument

noncomputable section

theorem moment_eq_periodMoment {d : ℕ} (f : Forms d) (j : ℕ) :
    moment f ((j + 1 : ℕ) : ℂ) = TernaryPeriodPolynomials.Argument.periodMoment f j := by
  rw [moment_succ_eq_integral, TernaryPeriodPolynomials.Argument.periodMoment]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Set.mem_Ioi] at ht
  rw [TernaryPeriodPolynomials.Argument.imaginaryAxisValue, dite_eq_left ht,
    UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ)) (by simpa using ht)]
  ring

theorem monomial_exponent_eq (d i : ℕ) (c : ℂ) :
    MvPolynomial.monomial (exponent d i) c =
      MvPolynomial.C c * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (d - i) := by
  rw [exponent, MvPolynomial.monomial_add_single, MvPolynomial.C_mul_X_pow_eq_monomial]

theorem period_eq_periodPolynomial {d : ℕ} (f : Forms d) :
    period f = TernaryPeriodPolynomials.Argument.periodPolynomial d f := by
  have hreflect : ∀ (g : ℕ → MvPolynomial (Fin 2) ℂ),
      ∑ j ∈ Finset.range (d + 1), g (d - j) = ∑ j ∈ Finset.range (d + 1), g j := by
    intro g
    simpa using Finset.sum_range_reflect g (d + 1)
  rw [period, TernaryPeriodPolynomials.Argument.periodPolynomial, ← hreflect]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjd : j ≤ d := by omega
  have e2 : d - (d - j) = j := by omega
  rw [monomial_exponent_eq, periodCoefficient, e2, Nat.choose_symm hjd,
    moment_eq_periodMoment f j]

theorem period_eq_sum_CXX {d : ℕ} (f : Forms d) :
    period f = ∑ j ∈ Finset.range (d + 1), C (periodCoefficient f j) * X 0 ^ j * X 1 ^ (d - j) := by
  rw [period]
  apply Finset.sum_congr rfl
  intro j _
  exact monomial_exponent_eq d j (periodCoefficient f j)

theorem oddPeriod_eq_sum_CXX {d : ℕ} (f : Forms d) :
    oddPeriod f =
      ∑ j ∈ (Finset.range (d + 1)).filter Odd,
        C (periodCoefficient f j) * X 0 ^ j * X 1 ^ (d - j) := by
  rw [oddPeriod]
  apply Finset.sum_congr rfl
  intro j _
  exact monomial_exponent_eq d j (periodCoefficient f j)

theorem flip_term (j k : ℕ) (c : ℂ) :
    bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ) (C c * X 0 ^ j * X 1 ^ k) =
      (-1) ^ j * (C c * X 0 ^ j * X 1 ^ k) := by
  simp only [map_mul, map_pow, bind₁_X_right, bind₁_C_right, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem flip_period_eq {d : ℕ} (f : Forms d) :
    bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ) (period f) =
      ∑ j ∈ Finset.range (d + 1),
        (-1) ^ j * (C (periodCoefficient f j) * X 0 ^ j * X 1 ^ (d - j)) := by
  rw [period_eq_sum_CXX, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact flip_term j (d - j) (periodCoefficient f j)

theorem term_sub_flip_eq (j k : ℕ) (c : ℂ) :
    (C c * X 0 ^ j * X 1 ^ k : MvPolynomial (Fin 2) ℂ) -
        (-1) ^ j * (C c * X 0 ^ j * X 1 ^ k) =
      if Odd j then 2 * (C c * X 0 ^ j * X 1 ^ k) else 0 := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [ite_eq_right (Nat.not_odd_iff_even.mpr hj), hj.neg_one_pow]; ring
  · rw [ite_eq_left hj, hj.neg_one_pow]; ring

theorem period_sub_flip_eq {d : ℕ} (f : Forms d) :
    period f - bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ) (period f) =
      2 * oddPeriod f := by
  rw [flip_period_eq, period_eq_sum_CXX, oddPeriod_eq_sum_CXX, Finset.mul_sum,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact term_sub_flip_eq j (d - j) (periodCoefficient f j)

theorem oddPeriod_eq_oddPeriodPart {d : ℕ} (f : Forms d) :
    oddPeriod f = TernaryPeriodPolynomials.Argument.oddPeriodPart d f := by
  rw [TernaryPeriodPolynomials.Argument.oddPeriodPart, ← period_eq_periodPolynomial,
    period_sub_flip_eq, MvPolynomial.smul_eq_C_mul]
  have h2 : (2 : MvPolynomial (Fin 2) ℂ) = MvPolynomial.C (2 : ℂ) :=
    (map_ofNat MvPolynomial.C 2).symm
  rw [h2, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ (two_ne_zero), map_one, one_mul]

theorem even_ten : Even 10 := by decide

theorem forms_ten_finrank_eq_one : Module.finrank ℂ (Forms 10) = 1 := by
  rw [forms_finrank 10 even_ten]
  decide

/-- The kernel of the (unconditional) odd-period map on `Forms 10` is trivially stable under
every prime Hecke operator, because `Forms 10` is one-dimensional: either `f = 0` (handled
directly) or `f` spans `Forms 10`, so `primeHecke 10 p f` is a scalar multiple of `f` and
`periodMap` kills it by linearity. -/
theorem kernel_stable_ten : KernelStable 10 even_ten := by
  intro p f hf
  by_cases hf0 : f = 0
  · simp [hf0, map_zero]
  · have hspan : (ℂ ∙ f) = ⊤ :=
      (finrank_eq_one_iff_of_nonzero f hf0).mp forms_ten_finrank_eq_one
    have hmem : primeHecke 10 p f ∈ ℂ ∙ f := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← hc, map_smul, hf, smul_zero]

theorem periodMap_ten_injective : Function.Injective (periodMap 10 even_ten) :=
  periodMap_injective_of_kernel_stable 10 even_ten kernel_stable_ten

theorem oddPeriod_ne_zero_of_ne_zero {f : Forms 10} (hf0 : f ≠ 0) : oddPeriod f ≠ 0 := by
  have h1 : periodMap 10 even_ten f ≠ 0 := fun h =>
    hf0 (periodMap_ten_injective (h.trans (map_zero _).symm))
  rw [← periodMap_coe 10 even_ten f]
  exact fun h => h1 (Subtype.ext h)

theorem oddPeriodPart_ne_zero_of_ne_zero {f : Forms 10} (hf0 : f ≠ 0) :
    TernaryPeriodPolynomials.Argument.oddPeriodPart 10 f ≠ 0 := by
  rw [← oddPeriod_eq_oddPeriodPart]
  exact oddPeriod_ne_zero_of_ne_zero hf0

theorem oddPeriod_mem_space (f : Forms 10) :
    oddPeriod f ∈ TernaryPoly.BinaryComplexPeriod.space ℂ 10 :=
  (mem_space_iff_threeTerm even_ten f).mpr (threeTermDefect_eq_zero even_ten f)

theorem oddPeriodPart_mem_oddPeriodSpace (f : Forms 10) :
    TernaryPeriodPolynomials.Argument.oddPeriodPart 10 f ∈
      TernaryPoly.Paper.oddPeriodSpace ℂ 10 := by
  rw [TernaryPoly.Paper.oddPeriodSpace_eq ℂ 10, ← oddPeriod_eq_oddPeriodPart]
  exact oddPeriod_mem_space f

theorem symmetricTenPeriod_ne_zero : symmetricTenPeriod ℂ ≠ 0 := by
  intro h
  have heval : MvPolynomial.eval (![3, 1] : Fin 2 → ℂ) (symmetricTenPeriod ℂ) = 0 := by
    rw [h, map_zero]
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  norm_num at heval

/-- For a nonzero weight-twelve level-one cusp form `h` (using the defeq `Forms 10 = CuspForm
levelOne 12`), `oddPeriodPart 10 h` lies in `oddPeriodSpace ℂ 10` and is nonzero. -/
theorem oddPeriodPart_mem_and_ne_zero {h : CuspForm levelOne 12} (hh0 : h ≠ 0) :
    TernaryPeriodPolynomials.Argument.oddPeriodPart 10 h ∈ TernaryPoly.Paper.oddPeriodSpace ℂ 10 ∧
      TernaryPeriodPolynomials.Argument.oddPeriodPart 10 h ≠ 0 :=
  ⟨oddPeriodPart_mem_oddPeriodSpace h, oddPeriodPart_ne_zero_of_ne_zero hh0⟩

/-- **Conjunct 2, odd/symmetric half of `example_degree_ten`.** For every nonzero weight-twelve
level-one cusp form `h`, `symmetricTenPeriod ℂ` is a nonzero scalar multiple of
`oddPeriodPart 10 h`. Both lie in the one-dimensional space `oddPeriodSpace ℂ 10`, and both are
nonzero, so they are proportional; the scalar is nonzero because `symmetricTenPeriod ℂ` is
nonzero. -/
theorem conjunct2_odd {h : CuspForm levelOne 12} (hh0 : h ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ symmetricTenPeriod ℂ = c • TernaryPeriodPolynomials.Argument.oddPeriodPart 10 h := by
  obtain ⟨hmem, hne⟩ := oddPeriodPart_mem_and_ne_zero hh0
  set S := TernaryPoly.Paper.oddPeriodSpace ℂ 10
  have hdim : Module.finrank ℂ S = 1 := oddPeriodSpace_ten_finrank_eq_one ℂ
  have hsmem : symmetricTenPeriod ℂ ∈ S := symmetricTenPeriod_mem_oddPeriodSpace
  set v : S := ⟨TernaryPeriodPolynomials.Argument.oddPeriodPart 10 h, hmem⟩ with hv_def
  set w : S := ⟨symmetricTenPeriod ℂ, hsmem⟩ with hw_def
  have hv0 : v ≠ 0 := fun hcontra => hne (congrArg Subtype.val hcontra)
  have hspan : (ℂ ∙ v) = ⊤ := (finrank_eq_one_iff_of_nonzero v hv0).mp hdim
  have hwmem : w ∈ ℂ ∙ v := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwmem
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    rw [hc0, zero_smul] at hc
    exact symmetricTenPeriod_ne_zero (congrArg Subtype.val hc.symm)
  · have hc' : (c • v : S).val = w.val := congrArg Subtype.val hc
    rw [Submodule.coe_smul] at hc'
    exact hc'.symm

end
