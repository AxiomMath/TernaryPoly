module

public import TernaryPeriodPolynomials.Polynomial.Divisibility

@[expose] public section


/-! A generic cancellation lemma: given `g ∣ P * (X i - c)` and `¬ (X i - c) ∣ g`, conclude
`g ∣ P`, built entirely from the project's substitution-based
`TernaryPoly.linear_factor_dvd_of_substitution_zero` (no Mathlib `Prime`/`Irreducible`/UFD
machinery is used or needed). Feeds the "prime peeling" argument in `Corollary15PartB.lean`.

The `hself0` hypothesis (that `c` is fixed by its own substitution at coordinate `i`) must be
supplied by the caller: it holds whenever `c` does not involve variable `i`, but is false for a
general `c` (e.g. `c = X i + X j` is not fixed by `update X i c`), so it cannot be proved inside
this lemma uniformly. -/


open MvPolynomial TernaryPoly

namespace TernaryPeriodPolynomials.Argument

/-- Cancel a linear factor `X i - c` from a divisibility `g ∣ P * (X i - c)`, given that it does
not already divide `g`. -/
theorem dvd_of_dvd_mul_linear_of_not_dvd {σ R : Type*} [CommRing R] [IsDomain R] [DecidableEq σ]
    {g P : MvPolynomial σ R} {i : σ} {c : MvPolynomial σ R}
    (hself0 : bind₁ (Function.update X i c) (X i - c) = 0)
    (hne : (X i - c : MvPolynomial σ R) ≠ 0)
    (hg : g ∣ P * (X i - c)) (hnd : ¬ (X i - c : MvPolynomial σ R) ∣ g) :
    g ∣ P := by
  obtain ⟨k, hk⟩ := hg
  have hgc : bind₁ (Function.update X i c) g ≠ 0 := fun h0 =>
    hnd (linear_factor_dvd_of_substitution_zero g i c h0)
  have h0 : bind₁ (Function.update X i c) P * bind₁ (Function.update X i c) (X i - c) =
      bind₁ (Function.update X i c) g * bind₁ (Function.update X i c) k := by
    rw [← map_mul, ← map_mul, hk]
  rw [hself0, mul_zero] at h0
  have hk0 : bind₁ (Function.update X i c) k = 0 :=
    (mul_eq_zero.mp h0.symm).resolve_left hgc
  obtain ⟨k', hk'⟩ := linear_factor_dvd_of_substitution_zero k i c hk0
  refine ⟨k', ?_⟩
  exact mul_right_cancel₀ hne (by rw [hk, hk']; ring)

end TernaryPeriodPolynomials.Argument
