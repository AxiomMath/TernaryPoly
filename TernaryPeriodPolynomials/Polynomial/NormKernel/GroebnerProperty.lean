module

public import TernaryPeriodPolynomials.Polynomial.NormKernel.Groebner
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


/-!
# Appendix D: the Gröbner property of the printed basis

For the lexicographic order `a > b > c` (`MonomialOrder.lex` on `Fin 3`, `X 0 > X 1 > X 2`), the
fourteen printed polynomials are monic with the printed leading monomials (`degree_groebnerBasis`),
generate `I = (d₄, d₆, d₇)`, and form a Gröbner basis of `I` (`groebnerBasis_isGroebner`): every
nonzero `f ∈ I` has `lm(f)` divisible by some `lm(gᵢ)`. The standard monomials (not divisible by any
`lm(gᵢ)`) are exactly the 28 printed monomials (`standard_iff`). Proof: polynomial division
(`MonomialOrder.div`) leaves a remainder supported on standard monomials and lying in `I`, which is
zero by `std_coeff_eq_zero_of_mem`.

Written by Claude Opus 5.5.
-/


noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixD

open MvPolynomial
open scoped MonomialOrder
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial dicksonIdeal)

/-- The exponent of `aⁱ bʲ cᵏ`. -/
def e3 (i j k : ℕ) : Fin 3 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k

/-- The exponent of a triple. -/
def e3t (t : ℕ × ℕ × ℕ) : Fin 3 →₀ ℕ := e3 t.1 t.2.1 t.2.2

theorem e3_lt_fst {i j k i' j' k' : ℕ} (h : i < i') :
    e3 i j k ≺[MonomialOrder.lex] e3 i' j' k' := by
  rw [MonomialOrder.lex_lt_iff]
  refine ⟨0, fun x hx => absurd hx (Fin.not_lt_zero x), ?_⟩
  simpa [e3] using h

theorem e3_lt_snd {i j k j' k' : ℕ} (h : j < j') :
    e3 i j k ≺[MonomialOrder.lex] e3 i j' k' := by
  rw [MonomialOrder.lex_lt_iff]
  refine ⟨1, fun x hx => ?_, ?_⟩
  · have : x = 0 := by omega
    subst this; simp [e3]
  · simpa [e3] using h

theorem e3_lt_thd {i j k k' : ℕ} (h : k < k') :
    e3 i j k ≺[MonomialOrder.lex] e3 i j k' := by
  rw [MonomialOrder.lex_lt_iff]
  refine ⟨2, fun x hx => ?_, ?_⟩
  · fin_cases x <;> simp_all [e3]
  · simpa [e3] using h

theorem monomial_e3 (i j k : ℕ) :
    monomial (e3 i j k) (1 : ZMod 2) = a ^ i * b ^ j * c ^ k := by
  rw [TernaryPoly.DicksonQuotient.a, TernaryPoly.DicksonQuotient.b, TernaryPoly.DicksonQuotient.c,
    X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, monomial_mul_monomial]
  simp [e3]

theorem e3t_injective : Function.Injective e3t := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  have h2 := congrArg (· 2) h
  simp [e3t, e3] at h0 h1 h2
  simp [h0, h1, h2]

theorem e3_le_iff {i j k i' j' k' : ℕ} : e3 i j k ≤ e3 i' j' k' ↔ i ≤ i' ∧ j ≤ j' ∧ k ≤ k' := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    exact ⟨by simpa [e3] using h 0, by simpa [e3] using h 1, by simpa [e3] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ x
    fin_cases x <;> simpa [e3]

theorem eq_e3 (e : Fin 3 →₀ ℕ) : e = e3 (e 0) (e 1) (e 2) := by
  ext x
  fin_cases x <;> simp [e3]

/-- Lexicographic `<` on exponent triples. -/
def tripleLT (t t' : ℕ × ℕ × ℕ) : Prop :=
  t.1 < t'.1 ∨ (t.1 = t'.1 ∧ (t.2.1 < t'.2.1 ∨ (t.2.1 = t'.2.1 ∧ t.2.2 < t'.2.2)))

instance : DecidableRel tripleLT := fun _ _ => by unfold tripleLT; infer_instance

theorem e3t_lt_of_tripleLT {t t' : ℕ × ℕ × ℕ} (h : tripleLT t t') :
    e3t t ≺[MonomialOrder.lex] e3t t' := by
  obtain ⟨i, j, k⟩ := t
  obtain ⟨i', j', k'⟩ := t'
  rcases h with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · exact e3_lt_fst h
  · simp only at h1; subst h1; exact e3_lt_snd h
  · simp only at h1 h2; subst h1; subst h2; exact e3_lt_thd h3

/-- The sum of the monomials of a list of exponent triples. -/
def polyOf (T : List (ℕ × ℕ × ℕ)) : Poly :=
  (T.map fun t => monomial (e3t t) (1 : ZMod 2)).sum

theorem coeff_polyOf (T : List (ℕ × ℕ × ℕ)) (e : Fin 3 →₀ ℕ) :
    (polyOf T).coeff e = (T.map fun t => if e3t t = e then (1 : ZMod 2) else 0).sum := by
  induction T with
  | nil => simp [polyOf]
  | cons t T ih =>
    simp only [polyOf, List.map_cons, List.sum_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial] at ih ⊢
    rw [ih]

theorem coeff_polyOf_eq_zero (T : List (ℕ × ℕ × ℕ)) (e : Fin 3 →₀ ℕ)
    (h : ∀ t ∈ T, e3t t ≠ e) : (polyOf T).coeff e = 0 := by
  rw [coeff_polyOf]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  simp [h t ht]

/-- The leading monomial of a sum of distinct monomials with a strictly largest one. -/
theorem degree_polyOf (t₀ : ℕ × ℕ × ℕ) (T : List (ℕ × ℕ × ℕ)) (hT : ∀ t ∈ T, tripleLT t t₀) :
    MonomialOrder.lex.degree (polyOf (t₀ :: T)) = e3t t₀ := by
  have hne : ∀ t ∈ T, e3t t ≠ e3t t₀ := fun t ht h =>
    (e3t_lt_of_tripleLT (hT t ht)).ne (congrArg _ h)
  have hd : (polyOf (t₀ :: T)).coeff (e3t t₀) ≠ 0 := by
    have : (polyOf (t₀ :: T)).coeff (e3t t₀) = 1 + (polyOf T).coeff (e3t t₀) := by
      simp [polyOf, coeff_monomial]
    rw [this, coeff_polyOf_eq_zero T _ hne]
    decide
  apply MonomialOrder.lex.toSyn.injective
  apply le_antisymm
  · rw [MonomialOrder.degree_le_iff]
    intro e he
    by_contra hlt
    rw [not_le] at hlt
    apply (mem_support_iff.mp he)
    apply coeff_polyOf_eq_zero
    intro t ht h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (lt_irrefl _ (h ▸ hlt))
    · exact (lt_asymm (e3t_lt_of_tripleLT (hT t ht)) (h ▸ hlt))
  · exact MonomialOrder.le_degree (mem_support_iff.mpr hd)

/-- The exponent triples of the fourteen printed polynomials, leading monomial first. -/
def gbTriples : Fin 14 → List (ℕ × ℕ × ℕ) :=
  ![[(4, 0, 0), (1, 0, 1), (0, 2, 0)],
    [(3, 2, 0), (1, 0, 2), (0, 2, 1)],
    [(3, 0, 1), (2, 2, 0), (1, 1, 1), (0, 0, 2)],
    [(2, 3, 0), (1, 2, 1), (0, 4, 0), (0, 1, 2)],
    [(2, 1, 1), (1, 0, 2)],
    [(2, 0, 2), (0, 4, 0)],
    [(1, 4, 0), (0, 0, 3)],
    [(1, 3, 1)],
    [(1, 1, 2), (0, 3, 1), (0, 0, 3)],
    [(1, 0, 3), (0, 5, 0)],
    [(0, 6, 0)],
    [(0, 4, 1), (0, 1, 3)],
    [(0, 2, 2)],
    [(0, 0, 4)]]

/-- The leading exponent triples `lm(gᵢ)`. -/
def lmTriple : Fin 14 → ℕ × ℕ × ℕ :=
  ![(4, 0, 0), (3, 2, 0), (3, 0, 1), (2, 3, 0), (2, 1, 1), (2, 0, 2), (1, 4, 0), (1, 3, 1), (1, 1, 2), (1, 0, 3), (0, 6, 0), (0, 4, 1), (0, 2, 2), (0, 0, 4)]

/-- The exponent triples of the 28 standard monomials (order of `standardMonomial`). -/
def stdTriple : Fin 28 → ℕ × ℕ × ℕ :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (2, 0, 0), (0, 0, 1), (1, 1, 0), (3, 0, 0), (0, 2, 0), (1, 0, 1), (2, 1, 0), (0, 1, 1), (1, 2, 0), (2, 0, 1), (3, 1, 0), (0, 0, 2), (0, 3, 0), (1, 1, 1), (2, 2, 0), (0, 2, 1), (1, 0, 2), (1, 3, 0), (0, 1, 2), (0, 4, 0), (1, 2, 1), (0, 0, 3), (0, 3, 1), (0, 5, 0), (0, 1, 3)]

theorem groebnerBasis_eq_polyOf (i : Fin 14) : groebnerBasis i = polyOf (gbTriples i) := by
  fin_cases i <;>
    simp [groebnerBasis, gbTriples, polyOf, e3t, monomial_e3] <;> ring

theorem gbTriples_lead (i : Fin 14) :
    ∃ T, gbTriples i = lmTriple i :: T ∧ ∀ t ∈ T, tripleLT t (lmTriple i) := by
  fin_cases i <;> exact ⟨_, rfl, by decide⟩

/-- **The printed leading monomials.** -/
theorem degree_groebnerBasis (i : Fin 14) :
    MonomialOrder.lex.degree (groebnerBasis i) = e3t (lmTriple i) := by
  obtain ⟨T, hT, hlt⟩ := gbTriples_lead i
  rw [groebnerBasis_eq_polyOf, hT, degree_polyOf _ _ hlt]

theorem groebnerBasis_ne_zero (i : Fin 14) : groebnerBasis i ≠ 0 := by
  intro h
  have := degree_groebnerBasis i
  rw [h, MonomialOrder.degree_zero] at this
  have h0 := congrArg (fun e => e 0 + e 1 + e 2) this
  fin_cases i <;> simp [lmTriple, e3t, e3] at h0

/-- **The printed polynomials are monic.** -/
theorem leadingCoeff_groebnerBasis (i : Fin 14) :
    MonomialOrder.lex.leadingCoeff (groebnerBasis i) = 1 := by
  have h : MonomialOrder.lex.leadingCoeff (groebnerBasis i) ≠ 0 :=
    MonomialOrder.leadingCoeff_ne_zero_iff.mpr (groebnerBasis_ne_zero i)
  revert h
  generalize MonomialOrder.lex.leadingCoeff (groebnerBasis i) = x
  revert x
  decide

theorem standardMonomial_eq_monomial (k : Fin 28) :
    standardMonomial k = monomial (e3t (stdTriple k)) 1 := by
  fin_cases k <;>
    simp [TernaryPoly.DicksonQuotient.standardMonomial, stdTriple, e3t, monomial_e3]

/-- Divisibility of exponent triples. -/
def tripleLE (t t' : ℕ × ℕ × ℕ) : Prop := t.1 ≤ t'.1 ∧ t.2.1 ≤ t'.2.1 ∧ t.2.2 ≤ t'.2.2

instance : DecidableRel tripleLE := fun _ _ => by unfold tripleLE; infer_instance

theorem std_finite_check : ∀ x : Fin 4, ∀ y : Fin 6, ∀ z : Fin 4,
    (∀ i : Fin 14, ¬ tripleLE (lmTriple i) (x.val, y.val, z.val)) →
      ∃ k : Fin 28, stdTriple k = (x.val, y.val, z.val) := by
  decide

theorem std_not_divisible : ∀ k : Fin 28, ∀ i : Fin 14, ¬ tripleLE (lmTriple i) (stdTriple k) := by
  decide

/-- **The standard monomials.** An exponent is not divisible by any leading monomial of the printed
basis iff it is one of the 28 printed standard monomials. -/
theorem standard_iff (e : Fin 3 →₀ ℕ) :
    (∀ i : Fin 14, ¬ MonomialOrder.lex.degree (groebnerBasis i) ≤ e) ↔
      ∃ k : Fin 28, e = e3t (stdTriple k) := by
  have hle : ∀ i : Fin 14, (MonomialOrder.lex.degree (groebnerBasis i) ≤ e ↔
      tripleLE (lmTriple i) (e 0, e 1, e 2)) := by
    intro i
    rw [degree_groebnerBasis, eq_e3 e]
    simp only [e3t, e3_le_iff, tripleLE]
    simp [e3]
  simp only [hle]
  constructor
  · intro h
    have hx : e 0 < 4 := by
      by_contra hx; exact h 0 ⟨by simp [lmTriple]; omega, by simp [lmTriple], by simp [lmTriple]⟩
    have hy : e 1 < 6 := by
      by_contra hy; exact h 10 ⟨by simp [lmTriple], by simp [lmTriple]; omega, by simp [lmTriple]⟩
    have hz : e 2 < 4 := by
      by_contra hz; exact h 13 ⟨by simp [lmTriple], by simp [lmTriple], by simp [lmTriple]; omega⟩
    obtain ⟨k, hk⟩ := std_finite_check ⟨_, hx⟩ ⟨_, hy⟩ ⟨_, hz⟩ h
    refine ⟨k, ?_⟩
    rw [hk]
    exact eq_e3 e
  · rintro ⟨k, rfl⟩ i
    have := std_not_divisible k i
    convert this using 2
    · simp [e3t, e3]


/-- A Gröbner basis of an ideal for a monomial order (Cox–Little–O'Shea, Def. 2.5.5): a family of
elements of `I` generating `I` such that the leading monomial of every nonzero element of `I` is
divisible by the leading monomial of some member of the family. -/
def IsGroebnerBasis {σ R ι : Type*} [CommSemiring R] (m : MonomialOrder σ)
    (G : ι → MvPolynomial σ R) (I : Ideal (MvPolynomial σ R)) : Prop :=
  (∀ i, G i ∈ I) ∧ Ideal.span (Set.range G) = I ∧
    ∀ f ∈ I, f ≠ 0 → ∃ i, m.degree (G i) ≤ m.degree f

theorem groebnerBasis_span : Ideal.span (Set.range groebnerBasis) = dicksonIdeal := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact groebnerBasis_mem i
  · unfold TernaryPoly.DicksonQuotient.dicksonIdeal
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Ideal.subset_span ⟨0, by simp [groebnerBasis, d4]; ring⟩
    · exact Ideal.subset_span ⟨2, by simp [groebnerBasis, d6]; ring⟩
    · exact Ideal.subset_span ⟨4, by simp [groebnerBasis, d7]; ring⟩

theorem stdTriple_injective : Function.Injective stdTriple := by
  decide

/-- A polynomial in `I` supported on standard monomials is zero. -/
theorem eq_zero_of_mem_of_standard (r : Poly) (hr : r ∈ dicksonIdeal)
    (hsupp : ∀ e ∈ r.support, ∀ i : Fin 14, ¬ MonomialOrder.lex.degree (groebnerBasis i) ≤ e) :
    r = 0 := by
  have hexp : r = ∑ k, C (r.coeff (e3t (stdTriple k))) * standardMonomial k := by
    ext e
    simp only [coeff_sum, coeff_C_mul, standardMonomial_eq_monomial, coeff_monomial, mul_ite,
      mul_one, mul_zero]
    by_cases he : e ∈ r.support
    · obtain ⟨k₀, hk₀⟩ := (standard_iff e).mp (hsupp e he)
      rw [Finset.sum_eq_single k₀]
      · rw [ite_eq_left hk₀.symm, hk₀]
      · intro k _ hk
        rw [ite_eq_right]
        intro h
        exact hk (stdTriple_injective (e3t_injective (h.trans hk₀)))
      · simp
    · rw [notMem_support_iff.mp he]
      symm
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · rw [h]; exact notMem_support_iff.mp he
      · rfl
  have hzero := std_coeff_eq_zero_of_mem (fun k => r.coeff (e3t (stdTriple k))) (hexp ▸ hr)
  rw [hexp]
  simp [hzero]

/-- **Appendix D: the printed fourteen polynomials form a monic Gröbner basis of
`I = (d₄, d₆, d₇)` for the lexicographic order `a > b > c`.** -/
theorem groebnerBasis_isGroebner :
    IsGroebnerBasis MonomialOrder.lex groebnerBasis dicksonIdeal := by
  refine ⟨groebnerBasis_mem, groebnerBasis_span, ?_⟩
  intro f hf hf0
  have hunit : ∀ i, IsUnit (MonomialOrder.lex.leadingCoeff (groebnerBasis i)) := by
    intro i; rw [leadingCoeff_groebnerBasis]; exact isUnit_one
  obtain ⟨g, r, hfr, hdeg, hrsupp⟩ := MonomialOrder.lex.div hunit f
  have hlc : Finsupp.linearCombination Poly groebnerBasis g ∈ dicksonIdeal := by
    rw [Finsupp.linearCombination_apply]
    exact Ideal.sum_mem _ fun i _ => by
      simp only [smul_eq_mul]; exact Ideal.mul_mem_left _ _ (groebnerBasis_mem i)
  have hr : r ∈ dicksonIdeal := by
    have : r = f - Finsupp.linearCombination Poly groebnerBasis g := by
      rw [hfr]; ring
    rw [this]
    exact sub_mem hf hlc
  have hr0 : r = 0 := eq_zero_of_mem_of_standard r hr fun e he i => hrsupp e he i
  rw [hr0, add_zero] at hfr
  have hcD : f.coeff (MonomialOrder.lex.degree f) ≠ 0 :=
    MonomialOrder.coeff_degree_ne_zero_iff.mpr hf0
  generalize hD : MonomialOrder.lex.degree f = D at hcD
  have hcD' := hcD
  rw [hfr, Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum] at hcD'
  obtain ⟨i, -, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcD'
  rw [smul_eq_mul] at hci
  have hgi : g i ≠ 0 := by
    intro h; rw [h, zero_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hci; exact hci rfl
  have h1 := MonomialOrder.le_degree (m := MonomialOrder.lex) (mem_support_iff.mpr hci)
  have h2 := hdeg i
  rw [hD] at h2
  have heq : MonomialOrder.lex.degree (groebnerBasis i * g i) = D :=
    MonomialOrder.lex.toSyn.injective (le_antisymm h2 (by rw [mul_comm]; exact h1))
  rw [MonomialOrder.degree_mul (groebnerBasis_ne_zero i) hgi] at heq
  exact ⟨i, heq ▸ le_self_add⟩

end TernaryPeriodPolynomials.Argument.AppendixD
