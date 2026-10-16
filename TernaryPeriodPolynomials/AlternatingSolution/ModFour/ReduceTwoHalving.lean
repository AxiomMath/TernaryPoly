module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section



/-! A short, self-contained "halving" lemma used in the proof of Theorem 5.2
(`mf:thm:main`), step `mf:lem:halving`: if `f : MvPolynomial (Fin 3) ℤ` reduces to zero mod
two, then every coefficient of `f` is even, so `f = C 2 * g` for some `g`. Depends only on
`Defs/ModFour.lean`. -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- If `f` reduces to zero mod two, then `f = C 2 * g` for some `g`. -/
theorem exists_half_of_reduceTwo_eq_zero {f : MvPolynomial (Fin 3) ℤ} (hf : reduceTwo f = 0) :
    ∃ g : MvPolynomial (Fin 3) ℤ, f = C 2 * g := by
  have hdvd : ∀ d : Fin 3 →₀ ℕ, (2 : ℤ) ∣ f.coeff d := by
    intro d
    have hc0 : (reduceTwo f).coeff d = 0 := by rw [hf]; simp
    have hc1 : (Int.castRingHom (ZMod 2)) (f.coeff d) = 0 := by
      rw [← coeff_map]; exact hc0
    have hc2 : ((f.coeff d : ℤ) : ZMod 2) = 0 := hc1
    have h2 : ((2 : ℕ) : ℤ) ∣ f.coeff d := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hc2
    exact_mod_cast h2
  choose c hc using hdvd
  refine ⟨∑ d ∈ f.support, monomial d (c d), ?_⟩
  calc f = ∑ d ∈ f.support, monomial d (f.coeff d) := (support_sum_monomial_coeff f).symm
    _ = ∑ d ∈ f.support, C 2 * monomial d (c d) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [C_mul_monomial, ← hc d]
    _ = C 2 * ∑ d ∈ f.support, monomial d (c d) := by rw [Finset.mul_sum]

end TernaryPeriodPolynomials.Argument
