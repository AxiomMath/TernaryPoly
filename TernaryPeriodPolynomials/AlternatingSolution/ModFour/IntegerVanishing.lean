module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Theorem

@[expose] public section



/-! Part (a) of `alternating_odd_degree_solution_eq_zero`: the integer case, by infinite 2-adic descent using
`even_coefficients_of_four_dvd_norm` repeatedly. -/

open MvPolynomial TernaryPeriodPolynomials.Argument

namespace TernaryPeriodPolynomials.Argument.ModFourMain

/-- Descent measure for Part (a): the sum of absolute values of coefficients. -/
noncomputable def coeffAbsSum (f : MvPolynomial (Fin 3) ℤ) : ℕ :=
  ∑ d ∈ f.support, (f.coeff d).natAbs

lemma coeffAbsSum_eq_zero_iff {f : MvPolynomial (Fin 3) ℤ} :
    coeffAbsSum f = 0 ↔ f = 0 := by
  unfold coeffAbsSum
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    ext d
    by_cases hd : d ∈ f.support
    · exact absurd (Int.natAbs_eq_zero.mp (h d hd)) (MvPolynomial.mem_support_iff.mp hd)
    · have hzero : f.coeff d = 0 := by
        by_contra hne
        exact hd (MvPolynomial.mem_support_iff.mpr hne)
      simpa using hzero
  · intro h d hd
    rw [h] at hd
    simp at hd

lemma hasOddMonomials_of_isHomogeneous_odd {f : MvPolynomial (Fin 3) ℤ} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) : HasOddMonomials f := by
  intro d hd
  have h := hf (MvPolynomial.mem_support_iff.mp hd)
  rw [Finsupp.weight_apply] at h
  rw [Finsupp.sum_fintype] at h
  · have hdn : d 0 + d 1 + d 2 = n := by
      simpa [Fin.sum_univ_three, Pi.one_apply, smul_eq_mul, mul_one] using h
    rwa [hdn]
  · intro i; simp

lemma threeTermNorm_C_mul {R : Type*} [CommRing R] (c : R) (g : MvPolynomial (Fin 3) R) :
    threeTermNorm (C c * g) = C c * threeTermNorm g := by
  have h1 : (bind₁ (![-X 1, X 0 - X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) R)) (C c) = C c := by
    simp
  have h2 : (bind₁ (![X 1 - X 0, -X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) R)) (C c) = C c := by
    simp
  simp only [threeTermNorm, map_mul, h1, h2]
  ring

lemma isHomogeneous_of_C_two_mul {f g : MvPolynomial (Fin 3) ℤ} {n : ℕ}
    (hfg : f = C 2 * g) (hf : f.IsHomogeneous n) : g.IsHomogeneous n := by
  intro d hd
  apply hf
  rw [hfg, MvPolynomial.coeff_C_mul]
  exact mul_ne_zero two_ne_zero hd

lemma isAlternating_of_C_two_mul {f g : MvPolynomial (Fin 3) ℤ}
    (hfg : f = C 2 * g) (halt : IsAlternating f) : IsAlternating g := by
  have hC2 : (C (2:ℤ) : MvPolynomial (Fin 3) ℤ) ≠ 0 := by simp
  intro σ
  have h1 := halt σ
  rw [hfg, map_mul] at h1
  have hrc : rename σ (C (2:ℤ) : MvPolynomial (Fin 3) ℤ) = C 2 := by
    rw [← MvPolynomial.algebraMap_eq]
    exact AlgHom.commutes (rename σ) 2
  rw [hrc, ← mul_smul_comm] at h1
  exact mul_left_cancel₀ hC2 h1

lemma coeffAbsSum_C_two_mul (g : MvPolynomial (Fin 3) ℤ) :
    coeffAbsSum (C 2 * g) = 2 * coeffAbsSum g := by
  unfold coeffAbsSum
  have hsupp : (C (2:ℤ) * g).support = g.support := by
    ext d
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul,
      ne_eq, mul_eq_zero, not_or]
    simp
  rw [hsupp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [MvPolynomial.coeff_C_mul, Int.natAbs_mul]
  norm_num

lemma vanishing_aux {n : ℕ} (hn : Odd n) (m : ℕ) :
    ∀ f : MvPolynomial (Fin 3) ℤ, coeffAbsSum f = m → f.IsHomogeneous n →
      IsAlternating f → threeTermNorm f = 0 → f = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro f hm hf halt hN
    by_cases hf0 : f = 0
    · exact hf0
    · have hodd : HasOddMonomials f := hasOddMonomials_of_isHomogeneous_odd hf hn
      have hN4 : ∃ g : MvPolynomial (Fin 3) ℤ, threeTermNorm f = C 4 * g :=
        ⟨0, by rw [hN]; ring⟩
      obtain ⟨g, hfg⟩ := even_coefficients_of_four_dvd_norm f halt hodd hN4
      have hg0 : g ≠ 0 := by
        intro h; apply hf0; rw [hfg, h]; ring
      have hgsum : coeffAbsSum f = 2 * coeffAbsSum g := by rw [hfg, coeffAbsSum_C_two_mul]
      have hglt : coeffAbsSum g < m := by
        rw [← hm, hgsum]
        have hpos : 0 < coeffAbsSum g := by
          rcases Nat.eq_zero_or_pos (coeffAbsSum g) with h0 | hpos
          · exact absurd (coeffAbsSum_eq_zero_iff.mp h0) hg0
          · exact hpos
        omega
      have hgH : g.IsHomogeneous n := isHomogeneous_of_C_two_mul hfg hf
      have hgA : IsAlternating g := isAlternating_of_C_two_mul hfg halt
      have hgN : threeTermNorm g = 0 := by
        have hT := threeTermNorm_C_mul (2:ℤ) g
        rw [← hfg, hN] at hT
        exact (mul_eq_zero.mp hT.symm).resolve_left (by simp)
      have hgz := ih (coeffAbsSum g) hglt g rfl hgH hgA hgN
      rw [hfg, hgz]; ring

theorem vanishing_of_odd_alternating_norm_zero_int {n : ℕ} (hn : Odd n)
    {f : MvPolynomial (Fin 3) ℤ} (hf : f.IsHomogeneous n) (halt : IsAlternating f)
    (hN : threeTermNorm f = 0) : f = 0 :=
  vanishing_aux hn (coeffAbsSum f) f rfl hf halt hN

end TernaryPeriodPolynomials.Argument.ModFourMain
