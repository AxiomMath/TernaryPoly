module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenAlgebra
public import TernaryPeriodPolynomials.Polynomial.Definitions
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section


/-!
# The dimension of `evenPeriodSpace F 10` is exactly one

No analogue of `TernaryPoly.Paper.oddPeriodSpace_eq` (bridging to the already-dimension-
computed `TernaryPoly.BinaryComplexPeriod.space`) exists for the even/alternating side (see the
docstring of `ExampleDegreeTenDimension.lean`). This file proves
`Module.finrank ℚ (evenPeriodSpace ℚ 10) = 1` directly, by an elementary coefficient argument:

* `evenPeriodSpace ℚ 10` consists of homogeneous-degree-10 `q` fixed by the sign-flip
  substitution `bind₁![-X0,X1]` (so only even-degree-in-`X0` monomials survive) and satisfying
  the two axis relations and the two-term relation from `PeriodRelations`.
* The sign-flip and axis conditions pin `q` down to a 2-parameter family
  `C c2 * p1 + C c4 * p2` where `p1 = X0^8*X1^2 - X0^2*X1^8`, `p2 = X0^6*X1^4 - X0^4*X1^6`
  (`reduction` below).
* The two-term relation forces `3 * c2 + c4 = 0` (`three_term_defect`), collapsing the family to
  the one-dimensional span of `p1 - 3*p2 = alternatingTenPeriod ℚ` (`main_combo`).

Combined with `alternatingTenPeriod_mem_evenPeriodSpace` (already proved, generic over any
`CommRing`, in `ExampleDegreeTenAlgebra.lean`) and base change
(`TernaryPoly.Paper.evenPeriod_finrank_baseChange`), this gives
`evenPeriodSpace_ten_finrank_eq_one` for every `Field F` `[CharZero F]`.
-/


open MvPolynomial TernaryPoly.Paper TernaryPeriodPolynomials.Argument

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspForms

/-! ## Finsupp/coefficient bookkeeping for `Fin 2` -/

theorem prod_support_eq_prod_univ_fin2 {R : Type*} [CommRing R]
    (d : Fin 2 →₀ ℕ) (g : Fin 2 → MvPolynomial (Fin 2) R) :
    ∏ i ∈ d.support, g i ^ d i = g 0 ^ d 0 * g 1 ^ d 1 := by
  rw [← Fin.prod_univ_two (fun i => g i ^ d i)]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Finsupp.mem_support_iff, not_not] at hi
  rw [hi, pow_zero]

theorem bind1_monomial_fin2 {R : Type*} [CommRing R] (f0 f1 : MvPolynomial (Fin 2) R)
    (d : Fin 2 →₀ ℕ) (r : R) :
    bind₁ (![f0, f1] : Fin 2 → MvPolynomial (Fin 2) R) (monomial d r) =
      C r * f0 ^ (d 0) * f1 ^ (d 1) := by
  rw [bind₁_monomial, prod_support_eq_prod_univ_fin2 d (![f0, f1] : Fin 2 → MvPolynomial (Fin 2) R)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem monomial_as_CX0X1 {R : Type*} [CommRing R] (d : Fin 2 →₀ ℕ) (r : R) :
    (monomial d r : MvPolynomial (Fin 2) R) = C r * X 0 ^ (d 0) * X 1 ^ (d 1) := by
  rw [monomial_eq, Finsupp.prod, prod_support_eq_prod_univ_fin2 d (fun i => (X i : MvPolynomial (Fin 2) R))]
  ring

theorem single_add_eval0 (a b : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) 0 = a := by
  simp [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]

theorem single_add_eval1 (a b : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) 1 = b := by
  simp [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]

theorem single_add_single_eq_self (d : Fin 2 →₀ ℕ) :
    Finsupp.single (0:Fin 2) (d 0) + Finsupp.single 1 (d 1) = d := by
  ext i
  fin_cases i
  · simp [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  · simp [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]

theorem single_add_eq_iff (a b a' b' : ℕ) :
    Finsupp.single (0:Fin 2) a + Finsupp.single 1 b = Finsupp.single (0:Fin 2) a' + Finsupp.single 1 b' ↔
      a = a' ∧ b = b' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg (fun f => f 0) h
      simpa [single_add_eval0] using this
    · have := congrArg (fun f => f 1) h
      simpa [single_add_eval1] using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem coeff_CX0X1 {R : Type*} [CommRing R] (r : R) (a b : ℕ) (e : Fin 2 →₀ ℕ) :
    (C r * X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) R).coeff e =
      if Finsupp.single (0:Fin 2) a + Finsupp.single 1 b = e then r else 0 := by
  have hd : (monomial (Finsupp.single (0:Fin 2) a + Finsupp.single 1 b) r :
      MvPolynomial (Fin 2) R) = C r * X 0 ^ a * X 1 ^ b := by
    rw [monomial_as_CX0X1, single_add_eval0, single_add_eval1]
  rw [← hd, MvPolynomial.coeff_monomial]

theorem coeff_X0X1 {R : Type*} [CommRing R] (a b : ℕ) (e : Fin 2 →₀ ℕ) :
    (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) R).coeff e =
      if Finsupp.single (0:Fin 2) a + Finsupp.single 1 b = e then 1 else 0 := by
  have h := coeff_CX0X1 (R:=R) 1 a b e
  simpa using h

theorem C_neg_one_pow {R : Type*} [CommRing R] (n : ℕ) :
    (C ((-1:R)^n) : MvPolynomial (Fin 2) R) = (-1)^n := by
  rw [map_pow, map_neg, map_one]

theorem C_mul_C {R : Type*} [CommRing R] (a b : R) :
    (C a * C b : MvPolynomial (Fin 2) R) = C (a * b) := (map_mul C a b).symm

/-! ## The four substitution lemmas -/

/-- Sign-flip substitution `bind₁![-X0,X1]`. -/
theorem coeff_bind1_signflip {R : Type*} [CommRing R] (q : MvPolynomial (Fin 2) R)
    (e : Fin 2 →₀ ℕ) :
    (bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) q).coeff e =
      (-1) ^ (e 0) * q.coeff e := by
  conv_lhs => rw [q.as_sum, map_sum]
  rw [MvPolynomial.coeff_sum]
  conv_rhs => rw [q.as_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [bind1_monomial_fin2, neg_pow]
  have e1 : (C (q.coeff d) * ((-1)^(d 0) * X 0 ^ (d 0)) * X 1 ^ (d 1) :
      MvPolynomial (Fin 2) R) =
        (C (q.coeff d) * (-1:MvPolynomial (Fin 2) R)^(d 0)) * X 0 ^ (d 0) * X 1 ^ (d 1) := by
    ring
  have step : (C (q.coeff d) * ((-1)^(d 0) * X 0 ^ (d 0)) * X 1 ^ (d 1) :
      MvPolynomial (Fin 2) R) = C (q.coeff d * (-1:R)^(d 0)) * X 0 ^ (d 0) * X 1 ^ (d 1) := by
    rw [e1, ← C_neg_one_pow, C_mul_C]
  rw [step, coeff_CX0X1, single_add_single_eq_self, MvPolynomial.coeff_monomial]
  by_cases h : d = e
  · rw [ite_eq_left h, ite_eq_left h, h]; ring
  · rw [ite_eq_right h, ite_eq_right h]; ring

theorem homog_sum_eq (d : Fin 2 →₀ ℕ) :
    (Finsupp.weight (1 : Fin 2 → ℕ)) d = d 0 + d 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  have hs : ∑ i ∈ d.support, d i • (1 : Fin 2 → ℕ) i = ∑ i ∈ d.support, d i := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hs, ← Fin.sum_univ_two (fun i => d i)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Finsupp.mem_support_iff, not_not] at hi
  exact hi

/-- Axis substitution `bind₁![X0,0]`. -/
theorem coeff_bind1_axis2 {R : Type*} [CommRing R] {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous 10) :
    (bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) R) q).coeff (Finsupp.single (0:Fin 2) 10) =
      q.coeff (Finsupp.single (0:Fin 2) 10) := by
  conv_lhs => rw [q.as_sum, map_sum]
  rw [MvPolynomial.coeff_sum]
  conv_rhs => rw [q.as_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : q.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hdeg : (Finsupp.weight (1:Fin 2→ℕ)) d = 10 := hq hd0
  rw [homog_sum_eq] at hdeg
  rw [bind1_monomial_fin2]
  rw [MvPolynomial.coeff_monomial]
  by_cases hd1 : d 1 = 0
  · have hd0eq : d 0 = 10 := by omega
    have hdeq : d = Finsupp.single (0:Fin 2) 10 := by
      have hsum := single_add_single_eq_self d
      rw [hd0eq, hd1, Finsupp.single_zero, add_zero] at hsum
      exact hsum.symm
    rw [hd1, pow_zero, mul_one, ite_eq_left hdeq, MvPolynomial.C_mul_X_pow_eq_monomial,
      MvPolynomial.coeff_monomial, hd0eq]
    simp
  · have hdne : d ≠ Finsupp.single (0:Fin 2) 10 := by
      intro hc; apply hd1; rw [hc]
      simp [Finsupp.single_eq_of_ne]
    rw [zero_pow hd1, mul_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_eq_right hdne]

/-- Axis substitution `bind₁![0,X1]`. -/
theorem coeff_bind1_axis1 {R : Type*} [CommRing R] {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous 10) :
    (bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) R) q).coeff (Finsupp.single (1:Fin 2) 10) =
      q.coeff (Finsupp.single (1:Fin 2) 10) := by
  conv_lhs => rw [q.as_sum, map_sum]
  rw [MvPolynomial.coeff_sum]
  conv_rhs => rw [q.as_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : q.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hdeg : (Finsupp.weight (1:Fin 2→ℕ)) d = 10 := hq hd0
  rw [homog_sum_eq] at hdeg
  rw [bind1_monomial_fin2]
  rw [MvPolynomial.coeff_monomial]
  by_cases hd0' : d 0 = 0
  · have hd1eq : d 1 = 10 := by omega
    have hdeq : d = Finsupp.single (1:Fin 2) 10 := by
      have hsum := single_add_single_eq_self d
      rw [hd0', hd1eq, Finsupp.single_zero, zero_add] at hsum
      exact hsum.symm
    rw [hd0', pow_zero, mul_one, ite_eq_left hdeq, MvPolynomial.C_mul_X_pow_eq_monomial,
      MvPolynomial.coeff_monomial, hd1eq]
    simp
  · have hdne : d ≠ Finsupp.single (1:Fin 2) 10 := by
      intro hc; apply hd0'; rw [hc]
      simp [Finsupp.single_eq_of_ne]
    rw [zero_pow hd0', mul_zero, zero_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_eq_right hdne]

/-- Two-term swap substitution `bind₁![-X1,X0]`. -/
theorem coeff_bind1_twoterm {R : Type*} [CommRing R] (q : MvPolynomial (Fin 2) R) (a b : ℕ) :
    (bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) R) q).coeff (Finsupp.single (0:Fin 2) a + Finsupp.single 1 b) =
      (-1) ^ b * q.coeff (Finsupp.single (0:Fin 2) b + Finsupp.single 1 a) := by
  conv_lhs => rw [q.as_sum, map_sum]
  rw [MvPolynomial.coeff_sum]
  conv_rhs => rw [q.as_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [bind1_monomial_fin2, neg_pow]
  have e1 : (C (q.coeff d) * ((-1) ^ (d 0) * X 1 ^ (d 0)) * X 0 ^ (d 1) :
      MvPolynomial (Fin 2) R) =
        (C (q.coeff d) * (-1 : MvPolynomial (Fin 2) R) ^ (d 0)) * X 0 ^ (d 1) * X 1 ^ (d 0) := by
    ring
  have step : (C (q.coeff d) * ((-1) ^ (d 0) * X 1 ^ (d 0)) * X 0 ^ (d 1) :
      MvPolynomial (Fin 2) R) =
        C (q.coeff d * (-1 : R) ^ (d 0)) * X 0 ^ (d 1) * X 1 ^ (d 0) := by
    rw [e1, ← C_neg_one_pow, C_mul_C]
  rw [step, coeff_CX0X1, MvPolynomial.coeff_monomial]
  simp only [single_add_eq_iff]
  by_cases h : d 1 = a ∧ d 0 = b
  · obtain ⟨h1, h0⟩ := h
    have hde : d = Finsupp.single (0:Fin 2) b + Finsupp.single 1 a := by
      rw [← single_add_single_eq_self d, h0, h1]
    rw [ite_eq_left ⟨h1, h0⟩, ite_eq_left hde, h0]
    ring
  · rw [ite_eq_right h]
    have hde : d ≠ Finsupp.single (0:Fin 2) b + Finsupp.single 1 a := by
      intro hc
      apply h
      constructor
      · have := congrArg (fun f => f 1) hc
        simpa [single_add_eval1] using this
      · have := congrArg (fun f => f 0) hc
        simpa [single_add_eval0] using this
    rw [ite_eq_right hde, mul_zero]

/-! ## The reduction to a 2-parameter family, and the three-term collapse -/

def p1 : MvPolynomial (Fin 2) ℚ := X 0 ^ 8 * X 1 ^ 2 - X 0 ^ 2 * X 1 ^ 8
def p2 : MvPolynomial (Fin 2) ℚ := X 0 ^ 6 * X 1 ^ 4 - X 0 ^ 4 * X 1 ^ 6

theorem three_term_defect (c2 c4 : ℚ)
    (h : (C c2 * p1 + C c4 * p2 : MvPolynomial (Fin 2) ℚ) +
        bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) (C c2 * p1 + C c4 * p2) +
        bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) (C c2 * p1 + C c4 * p2) = 0) :
    3 * c2 + c4 = 0 := by
  have heval := congrArg (MvPolynomial.eval (![3, 1] : Fin 2 → ℚ)) h
  simp only [p1, p2, map_add, map_sub, map_mul, map_pow, map_zero,
    bind₁_X_right, bind₁_C_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, MvPolynomial.eval_C, MvPolynomial.eval_X] at heval
  norm_num at heval
  linarith

theorem coeff_rhs (c2 c4 : ℚ) (a b : ℕ) :
    (C c2 * p1 + C c4 * p2 : MvPolynomial (Fin 2) ℚ).coeff (Finsupp.single (0:Fin 2) a + Finsupp.single 1 b) =
      c2 * (if 8 = a ∧ 2 = b then 1 else 0) - c2 * (if 2 = a ∧ 8 = b then 1 else 0) +
      (c4 * (if 6 = a ∧ 4 = b then 1 else 0) - c4 * (if 4 = a ∧ 6 = b then 1 else 0)) := by
  simp only [p1, p2, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sub, coeff_C_mul, coeff_X0X1, single_add_eq_iff]
  ring

theorem reduction (q : MvPolynomial (Fin 2) ℚ) (hq : q.IsHomogeneous 10)
    (ha2 : bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ha1 : bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ht2 : q + bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (he : bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = q) :
    ∃ c2 c4 : ℚ, q = C c2 * p1 + C c4 * p2 := by
  refine ⟨q.coeff (Finsupp.single (0:Fin 2) 8 + Finsupp.single 1 2),
    q.coeff (Finsupp.single (0:Fin 2) 6 + Finsupp.single 1 4), ?_⟩
  set c2 := q.coeff (Finsupp.single (0:Fin 2) 8 + Finsupp.single 1 2)
  set c4 := q.coeff (Finsupp.single (0:Fin 2) 6 + Finsupp.single 1 4)
  have hpar : ∀ e : Fin 2 →₀ ℕ, q.coeff e = (-1)^(e 0) * q.coeff e := by
    intro e
    have h := coeff_bind1_signflip q e
    rw [he] at h; exact h
  have hodd : ∀ e : Fin 2 →₀ ℕ, Odd (e 0) → q.coeff e = 0 := by
    intro e hoe
    have h := hpar e
    rw [hoe.neg_one_pow] at h
    linarith
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
      (C c2 * p1 + C c4 * p2).coeff (Finsupp.single (0:Fin 2) (10-k) + Finsupp.single 1 k) := by
    intro k hk
    rw [coeff_rhs]
    interval_cases k
    · norm_num
      have h := coeff_bind1_axis2 hq (R := ℚ)
      rw [ha2, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
      exact h.symm
    · norm_num
      apply hodd
      rw [single_add_eval0]; decide
    · norm_num
      rfl
    · norm_num
      apply hodd
      rw [single_add_eval0]; decide
    · norm_num
      rfl
    · norm_num
      apply hodd
      rw [single_add_eval0]; decide
    · have h := htwo 4 6
      norm_num at h ⊢
      linarith [h]
    · norm_num
      apply hodd
      rw [single_add_eval0]; decide
    · have h := htwo 2 8
      norm_num at h ⊢
      linarith [h]
    · norm_num
      apply hodd
      rw [single_add_eval0]; decide
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
    have hR : (C c2 * p1 + C c4 * p2).coeff d = 0 := by
      conv_lhs => rw [← single_add_single_eq_self d]
      rw [coeff_rhs]
      have e0 : ¬(8 = d 0 ∧ 2 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e1 : ¬(2 = d 0 ∧ 8 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e2 : ¬(6 = d 0 ∧ 4 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      have e3 : ¬(4 = d 0 ∧ 6 = d 1) := fun ⟨h1,h2⟩ => hdeg (by omega)
      rw [ite_eq_right e0, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3]
      ring
    rw [hL, hR]

theorem p1_sub_3p2_eq_altTen :
    p1 - 3 * p2 = (X 0^2 * X 1^2 * (X 0^2 - X 1^2)^3 : MvPolynomial (Fin 2) ℚ) := by
  simp only [p1, p2]; ring

theorem altTen_ne_zero :
    (X 0^2 * X 1^2 * (X 0^2 - X 1^2)^3 : MvPolynomial (Fin 2) ℚ) ≠ 0 := by
  intro h
  have heval : MvPolynomial.eval (![3,1] : Fin 2 → ℚ)
      (X 0^2 * X 1^2 * (X 0^2 - X 1^2)^3 : MvPolynomial (Fin 2) ℚ) = 0 := by rw [h, map_zero]
  simp only [map_mul, map_sub, map_pow, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  norm_num at heval

/-- The literal unfolding of `alternatingTenPeriod ℚ`, to bridge the real definition and the
elementary computation above (which was developed against the literal polynomial). -/
theorem alternatingTenPeriod_eq :
    (alternatingTenPeriod ℚ) = (X 0^2 * X 1^2 * (X 0^2 - X 1^2)^3 : MvPolynomial (Fin 2) ℚ) := rfl

theorem main_combo (q : MvPolynomial (Fin 2) ℚ) (hq : q.IsHomogeneous 10)
    (ha2 : bind₁ (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ha1 : bind₁ (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ht2 : q + bind₁ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (ht3 : q + bind₁ (![-X 1, X 0 - X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q +
        bind₁ (![X 1 - X 0, -X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = 0)
    (he : bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = q) :
    ∃ c : ℚ, q = C c * alternatingTenPeriod ℚ := by
  obtain ⟨c2, c4, hred⟩ := reduction q hq ha2 ha1 ht2 he
  have hdef : 3 * c2 + c4 = 0 := by
    apply three_term_defect c2 c4
    rw [hred] at ht3
    exact ht3
  refine ⟨c2, ?_⟩
  rw [hred, alternatingTenPeriod_eq, ← p1_sub_3p2_eq_altTen]
  have hc4 : c4 = -3 * c2 := by linarith
  rw [hc4]
  simp only [map_neg, map_mul, map_ofNat]
  ring

end TernaryPeriodPolynomials.Argument.CuspForms

namespace TernaryPeriodPolynomials.Argument

open TernaryPeriodPolynomials.Argument.CuspForms

/-- `evenPeriodSpace ℚ 10` is exactly the span of `alternatingTenPeriod ℚ`: every member is
pinned down by `main_combo` (via the `PeriodRelations` accessors and the sign-flip/kernel
condition unfolded from membership), and `alternatingTenPeriod ℚ` itself is a member
(`alternatingTenPeriod_mem_evenPeriodSpace`). -/
theorem evenPeriodSpace_ten_eq_span :
    evenPeriodSpace ℚ 10 = Submodule.span ℚ {alternatingTenPeriod ℚ} := by
  apply le_antisymm
  · intro q hq
    obtain ⟨⟨hhom, hrel⟩, hke⟩ := hq
    have he0 : bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q - q = 0 := hke
    have he : bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = q := by
      linear_combination he0
    obtain ⟨c, hc⟩ := main_combo q hhom hrel.axis_second hrel.axis_first hrel.two_term
      hrel.three_term he
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by rw [MvPolynomial.smul_eq_C_mul]; exact hc.symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact alternatingTenPeriod_mem_evenPeriodSpace (R := ℚ)

theorem evenPeriodSpace_ten_finrank_eq_one_rat :
    Module.finrank ℚ (evenPeriodSpace ℚ 10) = 1 := by
  rw [evenPeriodSpace_ten_eq_span]
  exact finrank_span_singleton (by rw [alternatingTenPeriod_eq]; exact altTen_ne_zero)

/-- **Dimension of `evenPeriodSpace` in degree ten.** The even/alternating analogue of
`oddPeriodSpace_ten_finrank_eq_one`, proved directly (no `evenPeriodSpace_eq` bridge exists;
see `ExampleDegreeTenDimension.lean`'s docstring) via `evenPeriodSpace_ten_eq_span` and base
change. -/
theorem evenPeriodSpace_ten_finrank_eq_one
    (F : Type*) [Field F] [CharZero F] :
    Module.finrank F (evenPeriodSpace F 10) = 1 := by
  rw [TernaryPoly.Paper.evenPeriod_finrank_baseChange F 10,
    evenPeriodSpace_ten_finrank_eq_one_rat]

end TernaryPeriodPolynomials.Argument
