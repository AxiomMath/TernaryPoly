module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalLieClass

@[expose] public section


/-!
# The radical Lie cohomology `H¹(𝔫, E_n) ≅ ℂ[X, Y]_{n+1}` of the plane parabolic

Paper: Appendix C, lines ~1365: "For the root operators `z∂_x, z∂_y`, the cocycle equation for
a pair `(a, b)` is `a_y = b_x`. Such a pair is the gradient of a homogeneous potential of degree
`n + 1`. Exact pairs are the gradients of potentials divisible by `z`, so the quotient is the
binary symmetric power of degree `n + 1`."

This file proves that statement for the model of `RadicalLieClass`: the polynomial Poincaré lemma
(`exists_potential_homogeneous`), that the potential-modulo-`Z` map `radicalContraction` has kernel
exactly the exact pairs (`radicalContraction_eq_zero_iff`) and is onto the degree-`n + 1` forms
(`exists_cocycle_with_contraction`), with the Euler identity
`radicalContraction_gradient`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- The polynomial antiderivative in the variable `i`: `X^s ↦ X^{s + e_i}/(s_i + 1)`. -/
def antiderivative (i : Fin 3) (c : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ :=
  ∑ s ∈ c.support, monomial (s + Finsupp.single i 1) (c.coeff s / ((s i : ℂ) + 1))

theorem pderiv_antiderivative (i : Fin 3) (c : MvPolynomial (Fin 3) ℂ) :
    pderiv i (antiderivative i c) = c := by
  conv_rhs => rw [c.as_sum]
  unfold antiderivative
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pderiv_monomial]
  simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  congr 1
  push_cast
  have : ((s i : ℂ) + 1) ≠ 0 := by
    have : ((s i + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  field_simp

theorem antiderivative_isHomogeneous (i : Fin 3) (c : MvPolynomial (Fin 3) ℂ) (n : ℕ)
    (hc : c.IsHomogeneous n) : (antiderivative i c).IsHomogeneous (n + 1) := by
  unfold antiderivative
  refine IsHomogeneous.sum _ _ (n + 1) fun s hs => ?_
  refine isHomogeneous_monomial _ ?_
  have := hc (mem_support_iff.mp hs)
  have h2 : Finsupp.degree s = n := by rw [Finsupp.degree_eq_weight_one]; exact this
  simp [h2]

/-- A polynomial with vanishing `X`-derivative has no monomial involving `X`. -/
theorem support_zero_of_pderiv_zero (c : MvPolynomial (Fin 3) ℂ) (hc : pderiv 0 c = 0)
    (s : Fin 3 →₀ ℕ) (hs : s ∈ c.support) : s 0 = 0 := by
  by_contra h0
  have hpos : 1 ≤ s 0 := Nat.one_le_iff_ne_zero.mpr h0
  set m : Fin 3 →₀ ℕ := s - Finsupp.single 0 1 with hm
  have hms : m + Finsupp.single 0 1 = s := by
    ext j
    simp only [hm, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hj : (0 : Fin 3) = j
    · subst hj; simp; omega
    · simp [hj]
  have := congrArg (·.coeff m) hc
  rw [coeff_pderiv, hms, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  have hne : ((m 0 : ℂ) + 1) ≠ 0 := by
    have : ((m 0 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  exact (mem_support_iff.mp hs) ((mul_eq_zero.mp this).resolve_right hne)

/-- Polynomial Poincaré lemma for the pair `(∂_X, ∂_Y)`: a closed homogeneous pair of degree `n`
is the gradient of a homogeneous potential of degree `n + 1`. -/
theorem exists_potential_homogeneous (n : ℕ) (a b : MvPolynomial (Fin 3) ℂ)
    (hab : pderiv 1 a = pderiv 0 b) (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n) :
    ∃ P, P.IsHomogeneous (n + 1) ∧ pderiv 0 P = a ∧ pderiv 1 P = b := by
  set Q := antiderivative 0 a with hQ
  have hQh : Q.IsHomogeneous (n + 1) := antiderivative_isHomogeneous 0 a n ha
  set c := b - pderiv 1 Q with hc
  have hch : c.IsHomogeneous n := by
    have : (pderiv 1 Q).IsHomogeneous n := by simpa using hQh.pderiv (i := 1)
    exact hb.sub this
  have hc0 : pderiv 0 c = 0 := by
    rw [hc, map_sub, pderiv_comm' 0 1 Q, hQ, pderiv_antiderivative, hab, sub_self]
  set R := antiderivative 1 c with hR
  have hR1 : pderiv 1 R = c := pderiv_antiderivative 1 c
  have hR0 : pderiv 0 R = 0 := by
    rw [hR]
    unfold antiderivative
    rw [map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [pderiv_monomial]
    have h0 := support_zero_of_pderiv_zero c hc0 s hs
    simp [h0]
  refine ⟨Q + R, hQh.add (antiderivative_isHomogeneous 1 c n hch), ?_, ?_⟩
  · rw [map_add, hR0, add_zero, hQ, pderiv_antiderivative]
  · rw [map_add, hR1, hc]; ring

/-- Reduction modulo `Z` leaves `P` unchanged modulo the ideal `(Z)`. -/
theorem X_two_dvd_sub_setZ (P : MvPolynomial (Fin 3) ℂ) :
    (X 2 : MvPolynomial (Fin 3) ℂ) ∣ P - setZ P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [setZ]
  | add p q hp hq =>
    rw [map_add, show p + q - (setZ p + setZ q) = (p - setZ p) + (q - setZ q) by ring]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, show p * X k - setZ p * setZ (X k) =
      (p - setZ p) * X k + setZ p * (X k - setZ (X k)) by ring]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    fin_cases k <;> simp [setZ]

theorem X_two_dvd_of_setZ_eq_zero (P : MvPolynomial (Fin 3) ℂ) (h : setZ P = 0) :
    (X 2 : MvPolynomial (Fin 3) ℂ) ∣ P := by
  simpa [h] using X_two_dvd_sub_setZ P

/-- Euler: the contraction of the gradient of a homogeneous potential `P` of degree `n + 1`
is `P` modulo `Z`. -/
theorem radicalContraction_gradient (n : ℕ) (P : MvPolynomial (Fin 3) ℂ)
    (hP : P.IsHomogeneous (n + 1)) :
    radicalContraction n (pderiv 0 P) (pderiv 1 P) = setZ P := by
  have hE := congrArg setZ hP.sum_X_mul_pderiv
  simp only [Fin.sum_univ_three, map_add, map_mul, nsmul_eq_mul, map_natCast] at hE
  have h0 : setZ (X 0 : MvPolynomial (Fin 3) ℂ) = X 0 := by simp [setZ]
  have h1 : setZ (X 1 : MvPolynomial (Fin 3) ℂ) = X 1 := by simp [setZ]
  have h2 : setZ (X 2 : MvPolynomial (Fin 3) ℂ) = 0 := by simp [setZ]
  rw [h0, h1, h2, zero_mul, add_zero] at hE
  unfold radicalContraction
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  have : X 0 * setZ (pderiv 0 P) + X 1 * setZ (pderiv 1 P) = C ((n : ℂ) + 1) * setZ P := by
    rw [hE]; simp
  rw [this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]

theorem isHomogeneous_of_X_two_mul (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ)
    (h : (X 2 * Q).IsHomogeneous (n + 1)) : Q.IsHomogeneous n := by
  intro m hm
  have hc : (X 2 * Q).coeff (m + Finsupp.single 2 1) ≠ 0 := by
    rwa [add_comm, coeff_X_mul]
  have := h hc
  have h2 : Finsupp.degree m = n := by
    have h3 : Finsupp.degree (m + Finsupp.single 2 1) = n + 1 := by
      rw [Finsupp.degree_eq_weight_one]; exact this
    simpa using h3
  rw [← h2, Finsupp.degree_eq_weight_one]
  rfl

/-- **The radical class map is injective on cohomology.** A closed homogeneous pair of degree `n`
has zero potential-modulo-`Z` class iff it is exact, `(a, b) = (ν₁ e, ν₂ e)` with `e` homogeneous
of degree `n`. -/
theorem radicalContraction_eq_zero_iff (n : ℕ) (a b : MvPolynomial (Fin 3) ℂ)
    (hab : IsRadicalCocycle a b) (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n) :
    radicalContraction n a b = 0 ↔
      ∃ e : MvPolynomial (Fin 3) ℂ, e.IsHomogeneous n ∧ a = radicalOpX e ∧ b = radicalOpY e := by
  constructor
  · intro h0
    obtain ⟨P, hP, hPa, hPb⟩ := exists_potential_homogeneous n a b
      ((isRadicalCocycle_iff a b).mp hab).symm ha hb
    subst hPa hPb
    rw [radicalContraction_gradient n P hP] at h0
    obtain ⟨Q, hQ⟩ := X_two_dvd_of_setZ_eq_zero P h0
    subst hQ
    refine ⟨-Q, (isHomogeneous_of_X_two_mul n Q hP).neg, ?_, ?_⟩
    · simp [radicalOpX, Derivation.leibniz, pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
    · simp [radicalOpY, Derivation.leibniz, pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
  · rintro ⟨e, -, rfl, rfl⟩
    exact radicalContraction_coboundary n e

/-- **The radical class map is onto the binary forms.** Every homogeneous potential `Q` of degree
`n + 1` is the potential of a closed homogeneous pair of degree `n`, namely its gradient. -/
theorem exists_cocycle_with_contraction (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ)
    (hQ : Q.IsHomogeneous (n + 1)) :
    ∃ a b : MvPolynomial (Fin 3) ℂ, IsRadicalCocycle a b ∧ a.IsHomogeneous n ∧
      b.IsHomogeneous n ∧ radicalContraction n a b = setZ Q := by
  refine ⟨pderiv 0 Q, pderiv 1 Q, ?_, ?_, ?_, radicalContraction_gradient n Q hQ⟩
  · rw [isRadicalCocycle_iff, pderiv_comm' 0 1 Q]
  · simpa using hQ.pderiv (i := 0)
  · simpa using hQ.pderiv (i := 1)

end TernaryPeriodPolynomials.Argument.SeedC3
