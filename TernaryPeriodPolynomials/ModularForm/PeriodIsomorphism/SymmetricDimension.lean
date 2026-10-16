module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.SymmetricBijection
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.Vanishing

@[expose] public section


/-!
# Corollary 1.4, second conjunct, symmetric half: the dimension formula

For every characteristic-zero field `F` and every `n : ℕ`,
`finrank F (symmetricSolutionSpace F n) = finrank ℂ (Forms n)`.

* If `n` is odd, both sides vanish: the left via `symmetricSolutionSpace_eq_bot`
  (`Vanishing.lean`), the right because a level-one cusp form of odd weight is zero
  (bridged here from `ModularForm.levelOne_odd_weight_eq_zero`).
* If `n` is even (including `n = 0`), the left side base-changes to `finrank ℚ
  (symmetricSolutionSpace ℚ n)` from any characteristic-zero field (in particular from `ℂ`),
  and over `ℂ` it matches `finrank ℂ (Forms n)` via `oddBijection` (`SymmetricBijection.lean`).
-/

open MvPolynomial TernaryPoly.Paper TernaryPoly.BinaryCuspPeriod

namespace TernaryPeriodPolynomials.Argument.Corollary14

/-- A level-one cusp form of odd weight is zero: bridged from the modular-form version via the
`CuspForm → ModularForm` coercion, whose coercion is pointwise-evaluation-preserving. -/
theorem forms_eq_zero_of_odd {d : ℕ} (hd : Odd d) (f : Forms d) : f = 0 := by
  have hodd2 : Odd ((d : ℤ) + 2) := by
    obtain ⟨k, hk⟩ := hd
    exact ⟨k + 1, by push_cast [hk]; ring⟩
  have h := ModularForm.levelOne_odd_weight_eq_zero hodd2 f
  ext z
  have hz := DFunLike.congr_fun h z
  simpa [← CuspForm.toModularFormₗ_eq_coe, CuspForm.toModularFormₗ_apply] using hz

theorem forms_finrank_eq_zero_of_odd {d : ℕ} (hd : Odd d) :
    Module.finrank ℂ (Forms d) = 0 := by
  have : Subsingleton (Forms d) :=
    ⟨fun f g => (forms_eq_zero_of_odd hd f).trans (forms_eq_zero_of_odd hd g).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- **Corollary 1.4, second conjunct, symmetric half.** -/
theorem symmetricSolution_finrank (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    Module.finrank F (symmetricSolutionSpace F n) = Module.finrank ℂ (Forms n) := by
  rcases Nat.even_or_odd n with he | ho
  · have h1 : Module.finrank ℂ (symmetricSolutionSpace ℂ n) = Module.finrank ℂ (Forms n) :=
      (oddBijection n he).symm.finrank_eq
    rw [symmetricSolution_finrank_baseChange F n, ← symmetricSolution_finrank_baseChange ℂ n, h1]
  · rw [symmetricSolutionSpace_eq_bot (Or.inr ho), forms_finrank_eq_zero_of_odd ho,
      finrank_bot]

end TernaryPeriodPolynomials.Argument.Corollary14
