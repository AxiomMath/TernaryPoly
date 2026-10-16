module

public import TernaryPeriodPolynomials.Polynomial.Definitions
public import TernaryPeriodPolynomials.Polynomial.Defs
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section


/-! Proof of Lemma 2.1 part (iii): there are no nonzero solutions of degree at most three.
Proved directly by finite linear algebra on the (at most ten) coefficients of each homogeneous
degree, not via the support theorem or `TernaryPeriodPolynomials.main`. Feeds
`TernaryPeriodPolynomials.solution_homogeneous_symmetric_alternating_parts`. -/


open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

/-- Degree-0 case of `degree_le_three_eq_zero`. -/
private theorem degree_zero_eq_zero {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 3) F) (hh : f.IsHomogeneous 0) (hf : Solution f) :
    f = 0 := by
  have hsupp : f.support ⊆ ({0} : Finset (Fin 3 →₀ ℕ)) := by
    intro d hd
    have hdeg : d.degree = 0 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (hh.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
    have h0 : d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 0 := by omega
    have hd0 : d = 0 := by
      ext i; fin_cases i <;> simp_all
    simp [hd0]
  have hC : f = MvPolynomial.C (f.coeff 0) := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [Finset.sum_subset hsupp]
    · rw [Finset.sum_singleton, MvPolynomial.monomial_zero']
    · intro d _ hd2
      simp [MvPolynomial.notMem_support_iff.mp hd2]
  have hbC : ∀ g : Fin 3 → Ternary F,
      bind₁ g (MvPolynomial.C (f.coeff 0) : Ternary F)
      = MvPolynomial.C (f.coeff 0) := by
    intro g
    simp
  have hzero : f.coeff (0 : Fin 3 →₀ ℕ) = 0 := by
    have hnorm := hf.norm
    rw [hC, hbC, hbC] at hnorm
    have h2 := congrArg (·.coeff (0 : Fin 3 →₀ ℕ)) hnorm
    simp [MvPolynomial.coeff_C] at h2
    linear_combination h2 / 3
  rw [hC, hzero]
  simp

/-- Degree-1 case of `degree_le_three_eq_zero`. -/
private theorem degree_one_eq_zero {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 3) F) (hh : f.IsHomogeneous 1) (hf : Solution f) :
    f = 0 := by
  set a := f.coeff (Finsupp.single 0 1 : Fin 3 →₀ ℕ) with ha
  set b := f.coeff (Finsupp.single 1 1 : Fin 3 →₀ ℕ) with hb
  set c := f.coeff (Finsupp.single 2 1 : Fin 3 →₀ ℕ) with hc
  have hsupp : f.support ⊆
      ({Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1} : Finset (Fin 3 →₀ ℕ)) := by
    intro d hd
    have hdeg : d.degree = 1 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (hh.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
    have h0 : d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 0 ∨ d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0 ∨
        d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 1 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h0 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · left; ext i; fin_cases i <;> simp_all
    · right; left; ext i; fin_cases i <;> simp_all
    · right; right; ext i; fin_cases i <;> simp_all
  have hC : f = MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
      + MvPolynomial.C c * MvPolynomial.X 2 := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [Finset.sum_subset hsupp]
    · rw [Finset.sum_insert (by simp [Finsupp.single_eq_single_iff]),
        Finset.sum_insert (by simp [Finsupp.single_eq_single_iff]), Finset.sum_singleton,
        ← MvPolynomial.C_mul_X_eq_monomial, ← MvPolynomial.C_mul_X_eq_monomial,
        ← MvPolynomial.C_mul_X_eq_monomial]
      ring
    · intro d _ hd2
      simp [MvPolynomial.notMem_support_iff.mp hd2]
  have hcyc := hf.cyclic
  rw [hC] at hcyc
  simp [bind₁_X_right] at hcyc
  have hnorm := hf.norm
  rw [hC] at hnorm
  simp [bind₁_X_right] at hnorm
  have e1 := congrArg (·.coeff (Finsupp.single 0 1 : Fin 3 →₀ ℕ)) hcyc
  have e2 := congrArg (·.coeff (Finsupp.single 1 1 : Fin 3 →₀ ℕ)) hcyc
  have e3 := congrArg (·.coeff (Finsupp.single 2 1 : Fin 3 →₀ ℕ)) hnorm
  simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Finsupp.single_eq_single_iff] at e1 e2 e3
  have hc0 : c = 0 := by linear_combination e3 / 3
  have ha0 : a = 0 := by linear_combination hc0 - e1
  have hb0 : b = 0 := by linear_combination ha0 - e2
  rw [hC, ha0, hb0, hc0]
  simp

/-- Degree-2 case of `degree_le_three_eq_zero`. -/
private theorem degree_two_eq_zero {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 3) F) (hh : f.IsHomogeneous 2) (hf : Solution f) :
    f = 0 := by
  have hFalse : ∀ {x y : Fin 3 →₀ ℕ}, x = y →
      x 0 ≠ y 0 ∨ x 1 ≠ y 1 ∨ x 2 ≠ y 2 → False := by
    intro x y h hor
    rcases hor with h0 | h1 | h2
    · exact h0 (congrArg (fun g => g 0) h)
    · exact h1 (congrArg (fun g => g 1) h)
    · exact h2 (congrArg (fun g => g 2) h)
  set p0 := f.coeff (Finsupp.single 0 2 : Fin 3 →₀ ℕ)
  set p1 := f.coeff (Finsupp.single 1 2 : Fin 3 →₀ ℕ)
  set p2 := f.coeff (Finsupp.single 2 2 : Fin 3 →₀ ℕ)
  set q01 := f.coeff (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 3 →₀ ℕ)
  set q02 := f.coeff (Finsupp.single 0 1 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
  set q12 := f.coeff (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
  have hsupp : f.support ⊆
      ({Finsupp.single 0 2, Finsupp.single 1 2, Finsupp.single 2 2,
        Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 0 1 + Finsupp.single 2 1,
        Finsupp.single 1 1 + Finsupp.single 2 1} : Finset (Fin 3 →₀ ℕ)) := by
    intro d hd
    have hdeg : d.degree = 2 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (hh.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
    have h0 : (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 0) ∨ (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 0) ∨
        (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 2) ∨ (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0) ∨
        (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 1) ∨ (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 1) := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h0 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩
    · exact Or.inl (by ext i; fin_cases i <;> simp_all)
    · exact Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all))
    · exact Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all)))
    · exact Or.inr (Or.inr (Or.inr
        (Or.inl (by ext i; fin_cases i <;> simp_all [Finsupp.add_apply]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by ext i; fin_cases i <;> simp_all [Finsupp.add_apply])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (by ext i; fin_cases i <;> simp_all [Finsupp.add_apply])))))
  have hC : f = MvPolynomial.C p0 * MvPolynomial.X 0 ^ 2 + MvPolynomial.C p1 * MvPolynomial.X 1 ^ 2
      + MvPolynomial.C p2 * MvPolynomial.X 2 ^ 2 + MvPolynomial.C q01 * MvPolynomial.X 0 * MvPolynomial.X 1
      + MvPolynomial.C q02 * MvPolynomial.X 0 * MvPolynomial.X 2
      + MvPolynomial.C q12 * MvPolynomial.X 1 * MvPolynomial.X 2 := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [Finset.sum_subset hsupp]
    · rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h | h | h | h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h | h | h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h | h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          intro h
          exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_singleton]
      simp only [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial,
        pow_one]
      ring
    · intro d _ hd2
      simp [MvPolynomial.notMem_support_iff.mp hd2]
  have hcyc := hf.cyclic
  rw [hC] at hcyc
  simp [bind₁_X_right] at hcyc
  have hnorm := hf.norm
  rw [hC] at hnorm
  simp [bind₁_X_right] at hnorm
  have k1 := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → F)) hcyc
  have k2 := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → F)) hcyc
  have k3 := congrArg (MvPolynomial.eval (![1, 1, 0] : Fin 3 → F)) hcyc
  have k4 := congrArg (MvPolynomial.eval (![1, 0, 1] : Fin 3 → F)) hcyc
  have k5 := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → F)) hnorm
  have k6 := congrArg (MvPolynomial.eval (![1, 1, 1] : Fin 3 → F)) hnorm
  simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_neg,
    Matrix.cons_val_zero, Matrix.cons_val_one] at k1 k2 k3 k4 k5 k6
  have hp2 : p2 = 0 := by linear_combination k5 / 3
  have hp0 : p0 = 0 := by linear_combination hp2 - k1
  have hp1 : p1 = 0 := by linear_combination hp0 - k2
  have hq01 : q01 = 0 := by linear_combination k6 - 2 * hp0 - 2 * hp1 - 3 * hp2
  have hq02 : q02 = 0 := by linear_combination k3 + hp1 - hp2 + hq01
  have hq12 : q12 = 0 := by linear_combination k4 + hp0 - hp1 + hq02
  rw [hC, hp0, hp1, hp2, hq01, hq02, hq12]
  simp

/-- Two finitely supported functions on `Fin 3` agreeing at `0, 1, 2` are equal. -/
private theorem finsupp3_ext {x y : Fin 3 →₀ ℕ} (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) : x = y := by
  ext i
  fin_cases i <;> assumption

/-- The ten ways of writing `3` as an ordered sum of three natural numbers. -/
private theorem nat_sum_three_cases (a b c : ℕ) (h : a + b + c = 3) :
    (a = 3 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 3 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 3) ∨
    (a = 2 ∧ b = 1 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 2 ∧ c = 0) ∨
    (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2) ∨ (a = 0 ∧ b = 1 ∧ c = 2) ∨
    (a = 1 ∧ b = 1 ∧ c = 1) := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  have hc : c ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | (exfalso; omega) | simp

/-- Degree-3 case of `degree_le_three_eq_zero`. -/
private theorem degree_three_eq_zero {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 3) F) (hh : f.IsHomogeneous 3) (hf : Solution f) :
    f = 0 := by
  have hFalse : ∀ {x y : Fin 3 →₀ ℕ}, x = y →
      x 0 ≠ y 0 ∨ x 1 ≠ y 1 ∨ x 2 ≠ y 2 → False := by
    intro x y h hor
    rcases hor with h0 | h1 | h2
    · exact h0 (congrArg (fun g => g 0) h)
    · exact h1 (congrArg (fun g => g 1) h)
    · exact h2 (congrArg (fun g => g 2) h)
  set t300 := f.coeff (Finsupp.single 0 3 : Fin 3 →₀ ℕ)
  set t030 := f.coeff (Finsupp.single 1 3 : Fin 3 →₀ ℕ)
  set t003 := f.coeff (Finsupp.single 2 3 : Fin 3 →₀ ℕ)
  set t210 := f.coeff (Finsupp.single 0 2 + Finsupp.single 1 1 : Fin 3 →₀ ℕ)
  set t201 := f.coeff (Finsupp.single 0 2 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
  set t120 := f.coeff (Finsupp.single 0 1 + Finsupp.single 1 2 : Fin 3 →₀ ℕ)
  set t021 := f.coeff (Finsupp.single 1 2 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
  set t102 := f.coeff (Finsupp.single 0 1 + Finsupp.single 2 2 : Fin 3 →₀ ℕ)
  set t012 := f.coeff (Finsupp.single 1 1 + Finsupp.single 2 2 : Fin 3 →₀ ℕ)
  set t111 := f.coeff
    (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 3 →₀ ℕ)
  have hsupp : f.support ⊆
      ({Finsupp.single 0 3, Finsupp.single 1 3, Finsupp.single 2 3,
        Finsupp.single 0 2 + Finsupp.single 1 1, Finsupp.single 0 2 + Finsupp.single 2 1,
        Finsupp.single 0 1 + Finsupp.single 1 2, Finsupp.single 1 2 + Finsupp.single 2 1,
        Finsupp.single 0 1 + Finsupp.single 2 2, Finsupp.single 1 1 + Finsupp.single 2 2,
        Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1} :
        Finset (Fin 3 →₀ ℕ)) := by
    intro d hd
    have hdeg : d.degree = 3 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (hh.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
    have h0 := nat_sum_three_cases (d 0) (d 1) (d 2) (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h0 with ⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|
      ⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩
    · exact Or.inl (finsupp3_ext (by simp [h0]) (by simp [h1]) (by simp [h2]))
    · exact Or.inr (Or.inl (finsupp3_ext (by simp [h0]) (by simp [h1]) (by simp [h2])))
    · exact Or.inr (Or.inr (Or.inl (finsupp3_ext (by simp [h0]) (by simp [h1]) (by simp [h2]))))
    · exact Or.inr (Or.inr (Or.inr
        (Or.inl (finsupp3_ext (by simp [Finsupp.add_apply, h0]) (by simp [Finsupp.add_apply, h1])
          (by simp [Finsupp.add_apply, h2])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (finsupp3_ext (by simp [Finsupp.add_apply, h0]) (by simp [Finsupp.add_apply, h1])
          (by simp [Finsupp.add_apply, h2]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (finsupp3_ext (by simp [Finsupp.add_apply, h0]) (by simp [Finsupp.add_apply, h1])
          (by simp [Finsupp.add_apply, h2])))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (finsupp3_ext (by simp [Finsupp.add_apply, h0]) (by simp [Finsupp.add_apply, h1])
          (by simp [Finsupp.add_apply, h2]))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (finsupp3_ext (by simp [Finsupp.add_apply, h0]) (by simp [Finsupp.add_apply, h1])
          (by simp [Finsupp.add_apply, h2])))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (finsupp3_ext (by simp [Finsupp.add_apply, h0]) (by simp [Finsupp.add_apply, h1])
          (by simp [Finsupp.add_apply, h2]))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (finsupp3_ext (by simp [Finsupp.add_apply, h0]) (by simp [Finsupp.add_apply, h1])
          (by simp [Finsupp.add_apply, h2]))))))))))
  have hC : f = MvPolynomial.C t300 * MvPolynomial.X 0 ^ 3 + MvPolynomial.C t030 * MvPolynomial.X 1 ^ 3
      + MvPolynomial.C t003 * MvPolynomial.X 2 ^ 3
      + MvPolynomial.C t210 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1
      + MvPolynomial.C t201 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2
      + MvPolynomial.C t120 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
      + MvPolynomial.C t021 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2
      + MvPolynomial.C t102 * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2
      + MvPolynomial.C t012 * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2
      + MvPolynomial.C t111 * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [Finset.sum_subset hsupp]
    · rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h|h|h|h|h|h|h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h|h|h|h|h|h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h|h|h|h|h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h|h|h|h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h|h|h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h|h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h|h) <;>
            exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          intro h
          exact hFalse h (by simp [Finsupp.add_apply])),
        Finset.sum_singleton]
      simp only [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial,
        pow_one]
      ring
    · intro d _ hd2
      simp [MvPolynomial.notMem_support_iff.mp hd2]
  have hcyc := hf.cyclic
  rw [hC] at hcyc
  simp [bind₁_X_right] at hcyc
  have hnorm := hf.norm
  rw [hC] at hnorm
  simp [bind₁_X_right] at hnorm
  have k1 := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → F)) hcyc
  have k2 := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → F)) hcyc
  have k3 := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → F)) hcyc
  have k4 := congrArg (MvPolynomial.eval (![1, 1, 0] : Fin 3 → F)) hcyc
  have k5 := congrArg (MvPolynomial.eval (![1, 0, 1] : Fin 3 → F)) hcyc
  have k6 := congrArg (MvPolynomial.eval (![1, -1, 0] : Fin 3 → F)) hcyc
  have k7 := congrArg (MvPolynomial.eval (![1, 0, -1] : Fin 3 → F)) hcyc
  have k8 := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → F)) hnorm
  have k9 := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → F)) hnorm
  have k10 := congrArg (MvPolynomial.eval (![1, -1, 0] : Fin 3 → F)) hnorm
  have k11 := congrArg (MvPolynomial.eval (![1, 1, 1] : Fin 3 → F)) hnorm
  simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_neg,
    Matrix.cons_val_zero, Matrix.cons_val_one] at k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11
  have hs : t003 = 0 := by linear_combination k8 / 3
  have ht300 : t300 = 0 := by linear_combination hs - k1
  have ht030 : t030 = 0 := by linear_combination hs + k3
  have k9' : t210 + t120 = 0 := by linear_combination -k9
  have ht120_eq_t210 : t120 = t210 := by linear_combination k10 / 3 + 2 * ht300 - 2 * ht030
  have ht210 : t210 = 0 := by linear_combination (k9' - ht120_eq_t210) / 2
  have ht120 : t120 = 0 := by linear_combination ht120_eq_t210 + ht210
  have hu : t201 + t102 = 0 := by linear_combination k4 - hs + ht030 + ht210 + ht120
  have hv : t201 - t102 = 0 := by
    linear_combination k6 + 2 * ht300 - hs - ht030 - ht210 + ht120
  have ht201 : t201 = 0 := by linear_combination (hu + hv) / 2
  have ht102 : t102 = 0 := by linear_combination (hu - hv) / 2
  have hu2 : t021 + t012 = 0 := by linear_combination k5 - ht030 + ht300 + ht201 + ht102
  have hv2 : t021 - t012 = 0 := by
    linear_combination k7 + ht030 + ht300 - 2 * hs - ht201 + ht102
  have ht021 : t021 = 0 := by linear_combination (hu2 + hv2) / 2
  have ht012 : t012 = 0 := by linear_combination (hu2 - hv2) / 2
  have ht111 : t111 = 0 := by
    linear_combination k11 - 3 * hs - ht210 - 2 * ht201 - ht120 - 2 * ht021
  rw [hC, ht300, ht030, hs, ht210, ht201, ht120, ht021, ht102, ht012, ht111]
  simp

/-- There are no nonzero solutions of degree at most three (Lemma 2.1, part (iii)). -/
theorem degree_le_three_eq_zero {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (f : MvPolynomial (Fin 3) F) (hn : n ≤ 3) (hh : f.IsHomogeneous n) (hf : Solution f) :
    f = 0 := by
  interval_cases n
  · exact degree_zero_eq_zero f hh hf
  · exact degree_one_eq_zero f hh hf
  · exact degree_two_eq_zero f hh hf
  · exact degree_three_eq_zero f hh hf

end TernaryPeriodPolynomials.Argument
