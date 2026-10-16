module

public import TernaryPeriodPolynomials.ModularForm.Period.Consumer
public import TernaryPeriodPolynomials.ModularForm.HeckeLSeries.LSeries

@[expose] public section


noncomputable section
open MvPolynomial
open scoped MatrixGroups

namespace TernaryPoly.BinaryCuspPeriod

/-- Cuspidality supplies the zeroth Fourier coefficient, without any eigenform assumption. -/
theorem coefficients_zero {d : ℕ} (f : Forms d) : coefficients f 0 = 0 := by
  have h := CuspFormClass.qExpansion_coeff_zero f
    (Subgroup.strictWidthInfty_pos 𝒮ℒ) (Subgroup.strictWidthInfty_mem_strictPeriods 𝒮ℒ)
  simpa [coefficients, Subgroup.strictWidthInfty_SL2Z] using h

/-- Actual cusp outer L-values are nonzero under explicit normalized Hecke coefficient equations.
Deriving these coefficient equations from a modular-form Hecke eigenvector is a separate gate. -/
theorem actual_LSeries_ne_zero_of_coefficient_equations {d : ℕ} (hd : 4 < d)
    (f : Forms d) (c : Nat.Primes → ℂ) (h1 : coefficients f 1 = 1)
    (hm : ∀ m n, m.Coprime n → coefficients f (m*n) = coefficients f m * coefficients f n)
    (hr : ∀ p : Nat.Primes, ∀ r : ℕ,
      coefficients f (p.val^(r+2)) = coefficients f p.val * coefficients f (p.val^(r+1)) -
        c p * coefficients f (p.val^r)) :
    LSeries (coefficients f) (d : ℂ) ≠ 0 :=
  BinaryHeckeEulerProduct.LSeries_nat_ne_zero (coefficients f) c d (coefficients_zero f) h1
    hm hr (lseries_summable hd f)

/-- The literal extreme coefficient of the actual cusp period is detected by the Euler product,
with every Hecke input retained as a visible hypothesis. -/
theorem actual_extreme_ne_zero_of_coefficient_equations {d : ℕ} (hd : 4 < d)
    (f : Forms d) (c : Nat.Primes → ℂ) (h1 : coefficients f 1 = 1)
    (hm : ∀ m n, m.Coprime n → coefficients f (m*n) = coefficients f m * coefficients f n)
    (hr : ∀ p : Nat.Primes, ∀ r : ℕ,
      coefficients f (p.val^(r+2)) = coefficients f p.val * coefficients f (p.val^(r+1)) -
        c p * coefficients f (p.val^r)) :
    (oddPeriod f).coeff (exponent d 1) ≠ 0 := by
  intro hz
  exact actual_LSeries_ne_zero_of_coefficient_equations hd f c h1 hm hr
    ((coeff_oddPeriod_extreme_eq_zero_iff hd f).mp hz)

end TernaryPoly.BinaryCuspPeriod
