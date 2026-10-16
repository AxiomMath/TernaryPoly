module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.PullbackCollapse

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): the final assembly. Bridges
`formPullback_leviMap_seedForm_eq`'s single-scalar-multiple-of-`seedForm n h q 0 2` form
(`q := leviMap A t p`) to `leviCoefficientAction A t (seedForm n (slashTwisted (n+3) A h) p i j)`,
by unfolding `leviCoefficientAction`/`slashTwisted` and using `bind_leviCoeffSubst_seedLinear`/
`seedTau_leviMap`. Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `seedForm n h q 0 2` reduces to `C (h (seedTau q)) * seedLinear q ^ n`: the bracket factor
`seedBeta q 0 * seedDTau 2 - seedBeta q 2 * seedDTau 0` is identically `1`. -/
theorem seedForm_zero_two_eq (n : ℕ) (h : ℂ → ℂ) (q : Fin 5 → ℝ) :
    seedForm n h q 0 2 = C (h (seedTau q)) * seedLinear q ^ n := by
  unfold seedForm
  congr 2
  simp only [seedBeta, seedDTau, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-- `leviCoefficientAction A t` applied to `seedForm n h' p i j` reduces, via
`bind_leviCoeffSubst_seedLinear`, to a single scalar multiple of `seedLinear (leviMap A t p) ^ n`.
-/
theorem leviCoefficientAction_seedForm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hdet : A.det ≠ 0) (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) (ht : t ≠ 0)
    (n : ℕ) (h' : ℂ → ℂ) (i j : Fin 5) :
    leviCoefficientAction A t (seedForm n h' p i j) =
      C (((A.det : ℂ) * t)⁻¹ * h' (seedTau p) *
          (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i) *
          (((A 1 0 : ℂ) * seedTau p + A 1 1) / (A.det : ℂ)) ^ n) *
        seedLinear (leviMap A t p) ^ n := by
  unfold leviCoefficientAction seedForm
  rw [map_mul, map_pow, bind_leviCoeffSubst_seedLinear A t p hdet hden ht,
      MvPolynomial.bind₁_C_right, mul_pow]
  simp only [← mul_assoc, ← map_mul, ← map_pow]
  congr 1
  congr 1
  push_cast
  ring

/-- The integer-power form of `slashTwisted`'s denominator exponent matches the natural-power
inverse used by `leviCoefficientAction_seedForm_eq`'s `(δ/d)^n` factor. -/
theorem zpow_neg_natCast_add_three (δ : ℂ) (n : ℕ) :
    δ ^ (-((n : ℤ) + 3)) = (δ ^ (n + 3))⁻¹ := by
  rw [show (-((n : ℤ) + 3)) = (-(((n + 3 : ℕ) : ℤ))) by push_cast; ring, zpow_neg, zpow_natCast]

/-- Clause (iii) of `seed_closed_equivariant`: the Levi transformation law for the seed. -/
theorem lemma_C3_iii (n : ℕ) (h : ℂ → ℂ) :
    ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ), 0 < A.det → 0 < t →
      ∀ p : Fin 5 → ℝ, 0 < p 3 → ∀ i j : Fin 5,
        formPullback (leviMap A t) (seedForm n h) p i j =
          leviCoefficientAction A t (seedForm n (slashTwisted (n + 3) A h) p i j) := by
  intro A t hdet ht p hp3 i j
  have hdetne : A.det ≠ 0 := ne_of_gt hdet
  have hdetC : (A.det : ℂ) ≠ 0 := by exact_mod_cast hdetne
  have hden := leviDenom_ne_zero A p hdet hp3
  have htne : t ≠ 0 := ne_of_gt ht
  have hexp : (-(((n + 3 : ℕ) : ℤ))) = -((n : ℤ) + 3) := by push_cast; ring
  have hslash : slashTwisted (n + 3) A h (seedTau p) =
      (A.det : ℂ) ^ (n + 3) * ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ (-((n : ℤ) + 3)) *
        h (seedTau (leviMap A t p)) := by
    unfold slashTwisted
    rw [← seedTau_leviMap A t p, hexp]
  rw [formPullback_leviMap_seedForm_eq A t p hden htne n h i j, seedForm_zero_two_eq,
      leviCoefficientAction_seedForm_eq A t p hdetne hden htne n
        (slashTwisted (n + 3) A h) i j, hslash, zpow_neg_natCast_add_three]
  rw [← mul_assoc, ← map_mul]
  congr 1
  congr 1
  have hdetn : (A.det : ℂ) ^ n ≠ 0 := pow_ne_zero n hdetC
  have hδn : ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ n ≠ 0 := pow_ne_zero n hden
  rw [div_pow, pow_add, pow_add, mul_inv]
  field_simp

end TernaryPeriodPolynomials.Argument
