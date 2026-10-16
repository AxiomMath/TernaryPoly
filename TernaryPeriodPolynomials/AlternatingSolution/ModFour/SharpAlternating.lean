module

public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-! Alternating property of the sharpness example for Theorem 5.2 (`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `f = (x+y+z)²(x-y)(x-z)(y-z)` is alternating. -/
theorem sharp_alternating :
    IsAlternating ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) := by
  intro σ
  have h6 : σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2 ∨
      σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 := by
    revert σ; decide
  rcases h6 with h | h | h | h | h | h <;> subst h <;>
    simp [map_mul, map_add, map_sub, map_pow, rename_X, Equiv.swap_apply_def,
      Equiv.Perm.sign_one, Equiv.Perm.sign_swap', Units.val_one, Units.val_neg, one_smul] <;>
    ring

end TernaryPeriodPolynomials.Argument
