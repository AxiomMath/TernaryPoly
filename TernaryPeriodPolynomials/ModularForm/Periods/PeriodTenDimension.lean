module

public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodTenDimension
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenLinearIndependence

@[expose] public section


/-!
# The dimension of `periodSpace ℚ 10` is exactly two

`EvenPeriodTenDimension.lean` pins down `evenPeriodSpace ℚ 10` (the sign-flip-even half of
`periodSpace ℚ 10`) by a coefficient argument. This file redoes the same style of argument
*without* the sign-flip hypothesis, directly on all of `periodSpace ℚ 10`:

* `axis_first`/`axis_second`/`two_term` alone pin a homogeneous degree-10 `q` down to a
  5-parameter family `C c1*m1 + C c2*p1 + C c3*m3 + C c4*p2 + C c5*m5` (`reduction5`), where
  `m1 = X0^9X1+X0X1^9`, `m3 = X0^7X1^3+X0^3X1^7`, `m5 = X0^5X1^5`, and `p1`, `p2` are the two
  monomials already used in `EvenPeriodTenDimension.lean`.
* Evaluating `three_term` at the points `(1,0)` and `(2,1)` gives two linear equations in
  `c1,c3,c5` alone (`eqI`, `eqII`) that force `(c1,c3,c5)` proportional to `(4,-25,42)`, i.e. the
  odd-indexed part of `q` is a scalar multiple `t` of `symmetricTenPeriod ℚ` (since
  `symmetricTenPeriod ℚ = 4*m1 - 25*m3 + 42*m5`, `symmetricTenPeriod_eq_m145`).
* Since `symmetricTenPeriod ℚ` already satisfies the full `three_term` identity on its own
  (`symmetricTenPeriod_periodRelations.three_term`) and the three-term operator is linear, the
  remaining even-indexed part `q - t • symmetricTenPeriod ℚ = C c2*p1 + C c4*p2` must itself
  satisfy `three_term`, which is exactly the hypothesis of the already-proven `three_term_defect`.
  This collapses it to a multiple of `alternatingTenPeriod ℚ` (`main_combo2`).

Combined with `symmetricTenPeriod_mem_oddPeriodSpace`/`alternatingTenPeriod_mem_evenPeriodSpace`
(already proved, generic, in `ExampleDegreeTenAlgebra.lean`) and base change
(`TernaryPoly.Paper.normalizedPeriod_finrank_baseChange`), this gives
`periodSpace_ten_finrank_eq_two` for every `Field F` `[CharZero F]`.
-/


open MvPolynomial TernaryPoly.Paper TernaryPeriodPolynomials.Argument

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspForms

/-! ## The 5-parameter reduction (no sign-flip hypothesis) -/

def m1 : MvPolynomial (Fin 2) ℚ := X 0 ^ 9 * X 1 ^ 1 + X 0 ^ 1 * X 1 ^ 9
def m3 : MvPolynomial (Fin 2) ℚ := X 0 ^ 7 * X 1 ^ 3 + X 0 ^ 3 * X 1 ^ 7
def m5 : MvPolynomial (Fin 2) ℚ := X 0 ^ 5 * X 1 ^ 5

theorem coeff_rhs5 (c1 c2 c3 c4 c5 : ℚ) (a b : ℕ) :
    (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5 : MvPolynomial (Fin 2) ℚ).coeff (Finsupp.single (0:Fin 2) a + Finsupp.single 1 b) =
      c1 * (if 9 = a ∧ 1 = b then 1 else 0) + c1 * (if 1 = a ∧ 9 = b then 1 else 0) +
      (c2 * (if 8 = a ∧ 2 = b then 1 else 0) - c2 * (if 2 = a ∧ 8 = b then 1 else 0)) +
      (c3 * (if 7 = a ∧ 3 = b then 1 else 0) + c3 * (if 3 = a ∧ 7 = b then 1 else 0)) +
      (c4 * (if 6 = a ∧ 4 = b then 1 else 0) - c4 * (if 4 = a ∧ 6 = b then 1 else 0)) +
      c5 * (if 5 = a ∧ 5 = b then 1 else 0) := by
  simp only [p1, p2, m1, m3, m5, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sub, coeff_C_mul, coeff_X0X1, single_add_eq_iff]
  ring

theorem reduction5 (q : MvPolynomial (Fin 2) ℚ) (hq : q.IsHomogeneous 10)
    (ha2 : bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ha1 : bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ht2 : q + bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0) :
    ∃ c1 c2 c3 c4 c5 : ℚ,
      q = C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5 := by
  refine ⟨q.coeff (Finsupp.single (0:Fin 2) 9 + Finsupp.single 1 1),
    q.coeff (Finsupp.single (0:Fin 2) 8 + Finsupp.single 1 2),
    q.coeff (Finsupp.single (0:Fin 2) 7 + Finsupp.single 1 3),
    q.coeff (Finsupp.single (0:Fin 2) 6 + Finsupp.single 1 4),
    q.coeff (Finsupp.single (0:Fin 2) 5 + Finsupp.single 1 5), ?_⟩
  set c1 := q.coeff (Finsupp.single (0:Fin 2) 9 + Finsupp.single 1 1)
  set c2 := q.coeff (Finsupp.single (0:Fin 2) 8 + Finsupp.single 1 2)
  set c3 := q.coeff (Finsupp.single (0:Fin 2) 7 + Finsupp.single 1 3)
  set c4 := q.coeff (Finsupp.single (0:Fin 2) 6 + Finsupp.single 1 4)
  set c5 := q.coeff (Finsupp.single (0:Fin 2) 5 + Finsupp.single 1 5)
  have h2eq : bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = -q := by
    linear_combination ht2
  have htwo : ∀ a b : ℕ, q.coeff (Finsupp.single (0:Fin 2) a + Finsupp.single 1 b) =
      (-1)^(b+1) * q.coeff (Finsupp.single (0:Fin 2) b + Finsupp.single 1 a) := by
    intro a b
    have h := coeff_bind1_twoterm q a b
    rw [h2eq, coeff_neg] at h
    rw [pow_succ]
    linear_combination -h
  have Hk : ∀ k : ℕ, k ≤ 10 →
      q.coeff (Finsupp.single (0:Fin 2) (10-k) + Finsupp.single 1 k) =
      (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5).coeff (Finsupp.single (0:Fin 2) (10-k) + Finsupp.single 1 k) := by
    intro k hk
    rw [coeff_rhs5]
    interval_cases k
    · norm_num
      have h := coeff_bind1_axis2 hq (R := ℚ)
      rw [ha2, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
      exact h.symm
    · norm_num
      rfl
    · norm_num
      rfl
    · norm_num
      rfl
    · norm_num
      rfl
    · norm_num
      rfl
    · have h := htwo 4 6
      norm_num at h ⊢
      linarith [h]
    · have h := htwo 3 7
      norm_num at h ⊢
      linarith [h]
    · have h := htwo 2 8
      norm_num at h ⊢
      linarith [h]
    · have h := htwo 1 9
      norm_num at h ⊢
      linarith [h]
    · norm_num
      have h := coeff_bind1_axis1 hq (R := ℚ)
      rw [ha1, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
      exact h.symm
  apply MvPolynomial.ext
  intro d
  by_cases hdeg : d 0 + d 1 = 10
  · have hde : d = Finsupp.single (0:Fin 2) (10 - d 1) + Finsupp.single 1 (d 1) := by
      conv_lhs => rw [← single_add_single_eq_self d]
      congr 2
      omega
    rw [hde]
    exact Hk (d 1) (by omega)
  · have hL : q.coeff d = 0 := by
      by_contra hne
      exact hdeg (by rw [← homog_sum_eq]; exact hq hne)
    have hR : (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5).coeff d = 0 := by
      conv_lhs => rw [← single_add_single_eq_self d]
      rw [coeff_rhs5]
      have e1a : ¬(9 = d 0 ∧ 1 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e1b : ¬(1 = d 0 ∧ 9 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e2a : ¬(8 = d 0 ∧ 2 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e2b : ¬(2 = d 0 ∧ 8 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e3a : ¬(7 = d 0 ∧ 3 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e3b : ¬(3 = d 0 ∧ 7 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e4a : ¬(6 = d 0 ∧ 4 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e4b : ¬(4 = d 0 ∧ 6 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e5 : ¬(5 = d 0 ∧ 5 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      rw [ite_eq_right e1a, ite_eq_right e1b, ite_eq_right e2a, ite_eq_right e2b, ite_eq_right e3a, ite_eq_right e3b,
        ite_eq_right e4a, ite_eq_right e4b, ite_eq_right e5]
      ring
    rw [hL, hR]

/-! ## The three-term relation at two points, and the collapse to `span {sym, alt}` -/

theorem eqI (c1 c2 c3 c4 c5 : ℚ)
    (h : (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5 : MvPolynomial (Fin 2) ℚ) +
        bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)
          (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5) +
        bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ)
          (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5) = 0) :
    2 * c1 + 2 * c3 + c5 = 0 := by
  have heval := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → ℚ)) h
  simp only [m1, p1, m3, p2, m5, map_add, map_sub, map_mul, map_pow, map_zero,
    bind₁_X_right, bind₁_C_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, MvPolynomial.eval_C, MvPolynomial.eval_X] at heval
  norm_num at heval
  linarith

theorem eqII (c1 c2 c3 c4 c5 : ℚ)
    (h : (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5 : MvPolynomial (Fin 2) ℚ) +
        bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)
          (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5) +
        bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ)
          (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5) = 0) :
    1026 * c1 + 270 * c3 + 63 * c5 = 0 := by
  have heval := congrArg (MvPolynomial.eval (![2, 1] : Fin 2 → ℚ)) h
  simp only [m1, p1, m3, p2, m5, map_add, map_sub, map_mul, map_pow, map_zero,
    bind₁_X_right, bind₁_C_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, MvPolynomial.eval_C, MvPolynomial.eval_X] at heval
  norm_num at heval
  linarith

theorem symmetricTenPeriod_eq_m145 :
    (symmetricTenPeriod ℚ) = C (4:ℚ) * m1 - C (25:ℚ) * m3 + C (42:ℚ) * m5 := by
  show (X 0 * X 1 * (X 0 ^ 2 - X 1 ^ 2) ^ 2 * (X 0 ^ 2 - 4 * X 1 ^ 2) * (4 * X 0 ^ 2 - X 1 ^ 2) :
      MvPolynomial (Fin 2) ℚ) = C (4:ℚ) * m1 - C (25:ℚ) * m3 + C (42:ℚ) * m5
  simp only [m1, m3, m5, map_ofNat]
  ring

theorem threeTermOp_sub (a b : MvPolynomial (Fin 2) ℚ) (r : ℚ) :
    (a - C r * b) + bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) (a - C r * b) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) (a - C r * b) =
    (a + bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) a +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) a) -
    C r * (b + bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) b +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) b) := by
  simp only [map_sub, map_mul, bind₁_C_right]
  ring

theorem main_combo2 (q : MvPolynomial (Fin 2) ℚ) (hq : q.IsHomogeneous 10)
    (ha2 : bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ha1 : bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ht2 : q + bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ht3 : q + bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q +
        bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0) :
    ∃ s t : ℚ, q = C s * symmetricTenPeriod ℚ + C t * alternatingTenPeriod ℚ := by
  obtain ⟨c1, c2, c3, c4, c5, hred⟩ := reduction5 q hq ha2 ha1 ht2
  have ht3' : (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5 :
      MvPolynomial (Fin 2) ℚ) +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)
        (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ)
        (C c1 * m1 + C c2 * p1 + C c3 * m3 + C c4 * p2 + C c5 * m5) = 0 := by
    rw [← hred]; exact ht3
  have hI : 2 * c1 + 2 * c3 + c5 = 0 := eqI c1 c2 c3 c4 c5 ht3'
  have hII : 1026 * c1 + 270 * c3 + 63 * c5 = 0 := eqII c1 c2 c3 c4 c5 ht3'
  set t := c1 / 4 with ht_def
  have hc1' : c1 = 4 * t := by rw [ht_def]; ring
  have hc3' : c3 = -25 * t := by rw [ht_def]; linarith
  have hc5' : c5 = 42 * t := by rw [ht_def]; linarith
  have hqsplit : q = C t * symmetricTenPeriod ℚ + (C c2 * p1 + C c4 * p2) := by
    rw [hred, symmetricTenPeriod_eq_m145, hc1', hc3', hc5']
    simp only [map_mul, map_neg, map_ofNat]
    ring
  have hsym3 : (symmetricTenPeriod ℚ) +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) (symmetricTenPeriod ℚ) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) (symmetricTenPeriod ℚ) = 0 :=
    symmetricTenPeriod_periodRelations.three_term
  have hdefect : (C c2 * p1 + C c4 * p2 : MvPolynomial (Fin 2) ℚ) +
      bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) (C c2 * p1 + C c4 * p2) +
      bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) (C c2 * p1 + C c4 * p2) = 0 := by
    have hlin : (C c2 * p1 + C c4 * p2 : MvPolynomial (Fin 2) ℚ) =
        q - C t * symmetricTenPeriod ℚ := by
      rw [hqsplit]; ring
    rw [hlin, threeTermOp_sub, ht3, hsym3]
    ring
  have h34 : 3 * c2 + c4 = 0 := three_term_defect c2 c4 hdefect
  refine ⟨t, c2, ?_⟩
  rw [hqsplit]
  congr 1
  rw [alternatingTenPeriod_eq, ← p1_sub_3p2_eq_altTen]
  have hc4 : c4 = -3 * c2 := by linarith
  rw [hc4]
  simp only [map_neg, map_mul, map_ofNat]
  ring

theorem linearIndependent_tenPeriod :
    LinearIndependent ℚ ![symmetricTenPeriod ℚ, alternatingTenPeriod ℚ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul] at hst
  have hflip : bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)
      (C s * symmetricTenPeriod ℚ + C t * alternatingTenPeriod ℚ) = 0 := by rw [hst, map_zero]
  rw [map_add, map_mul, map_mul, bind₁_C_right, bind₁_C_right, symmetricTenPeriod_oddX,
    alternatingTenPeriod_evenX] at hflip
  have halt : (2 : MvPolynomial (Fin 2) ℚ) * (C t * alternatingTenPeriod ℚ) = 0 := by
    linear_combination hst + hflip
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp halt with h2 | hct
    · exact absurd h2 (by norm_num)
    · rcases mul_eq_zero.mp hct with hc | ha
      · exact (MvPolynomial.C_inj ℚ t 0).mp (hc.trans (map_zero C).symm)
      · exact absurd ha (alternatingTenPeriod_ne_zero' ℚ)
  have hsym : C s * symmetricTenPeriod ℚ = 0 := by
    rw [ht0, map_zero, zero_mul, add_zero] at hst; exact hst
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hsym with hc | hs
    · exact (MvPolynomial.C_inj ℚ s 0).mp (hc.trans (map_zero C).symm)
    · exact absurd hs (symmetricTenPeriod_ne_zero' ℚ)
  exact ⟨hs0, ht0⟩

end TernaryPeriodPolynomials.Argument.CuspForms

namespace TernaryPeriodPolynomials.Argument

open TernaryPeriodPolynomials.Argument.CuspForms

/-- `periodSpace ℚ 10` is exactly the span of `symmetricTenPeriod ℚ` and
`alternatingTenPeriod ℚ`: every member is pinned down by `main_combo2`, and both periods are
themselves members (`symmetricTenPeriod_mem_oddPeriodSpace`/`alternatingTenPeriod_mem_evenPeriodSpace`,
whose first component is exactly `periodSpace` membership). -/
theorem periodSpace_ten_eq_span_rat :
    periodSpace ℚ 10 = Submodule.span ℚ {symmetricTenPeriod ℚ, alternatingTenPeriod ℚ} := by
  apply le_antisymm
  · intro q hq
    obtain ⟨hhom, hrel⟩ := hq
    obtain ⟨s, t, hst⟩ := main_combo2 q hhom hrel.axis_second hrel.axis_first hrel.two_term
      hrel.three_term
    have hsmem : symmetricTenPeriod ℚ ∈
        Submodule.span ℚ ({symmetricTenPeriod ℚ, alternatingTenPeriod ℚ} : Set _) :=
      Submodule.subset_span (by simp)
    have hamem : alternatingTenPeriod ℚ ∈
        Submodule.span ℚ ({symmetricTenPeriod ℚ, alternatingTenPeriod ℚ} : Set _) :=
      Submodule.subset_span (by simp)
    rw [hst]
    have e1 : C s * symmetricTenPeriod ℚ = s • symmetricTenPeriod ℚ := by
      rw [MvPolynomial.smul_eq_C_mul]
    have e2 : C t * alternatingTenPeriod ℚ = t • alternatingTenPeriod ℚ := by
      rw [MvPolynomial.smul_eq_C_mul]
    rw [e1, e2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hsmem) (Submodule.smul_mem _ _ hamem)
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact symmetricTenPeriod_mem_oddPeriodSpace.1
    · rw [hx]; exact alternatingTenPeriod_mem_evenPeriodSpace.1

private theorem range_pair_eq (a b : MvPolynomial (Fin 2) ℚ) :
    Set.range (![a, b] : Fin 2 → MvPolynomial (Fin 2) ℚ) = ({a, b} : Set (MvPolynomial (Fin 2) ℚ)) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem periodSpace_ten_finrank_eq_two_rat :
    Module.finrank ℚ (periodSpace ℚ 10) = 2 := by
  rw [periodSpace_ten_eq_span_rat, ← range_pair_eq, finrank_span_eq_card linearIndependent_tenPeriod,
    Fintype.card_fin]

/-- **Dimension of `periodSpace` in degree ten.** Proved directly via
`periodSpace_ten_eq_span_rat` and base change, for every `Field F` `[CharZero F]`. -/
theorem periodSpace_ten_finrank_eq_two
    (F : Type*) [Field F] [CharZero F] :
    Module.finrank F (periodSpace F 10) = 2 := by
  rw [TernaryPoly.Paper.normalizedPeriod_finrank_baseChange F 10,
    periodSpace_ten_finrank_eq_two_rat]

end TernaryPeriodPolynomials.Argument
