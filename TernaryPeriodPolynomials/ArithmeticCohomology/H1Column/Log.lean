module

public import TernaryPeriodPolynomials.ArithmeticCohomology.H1Column.LogExp
public import TernaryPeriodPolynomials.ArithmeticCohomology.H1Column.LogSeries

@[expose] public section


/-!
# MR-8: `log ρ(U_ij) = -x_j ∂_{x_i}` on `E = Sym^n((ℚ³)*)` (`eq:table-weights`)

Formalized by Claude Sonnet 5.5.  Paper: "on dual polynomial coefficients, `log ρ(U_ij) = -x_j ∂_{x_i}`".

`E_n = HomogeneousPoly n` with the left inverse-substitution representation `integralAction n 0` of `GL₃(ℤ)` (no determinant twist), `U_ij = 1 + E_ij` (`unipotentGL`), `lieOpH n i j` the endomorphism `-x_j ∂_{x_i}` of `E_n`.

* `lieOpH_apply`: `lieOpH n i j f = -x_j · ∂f/∂x_i`.
* `isNilpotent_lieOpH`: it is nilpotent (indeed `(lieOpH n i j)^(n+1) = 0`).
* `rho_unipotent_eq_exp`: `ρ(U_ij) = exp(-x_j ∂_{x_i})` (`IsNilpotent.exp`).
* `log_rho_unipotent`: the logarithm series `∑_{k<n+1} (-1)^k/(k+1) (ρ(U_ij) - 1)^{k+1}` (finite, since `ρ(U_ij) - 1` is nilpotent) is exactly `-x_j ∂_{x_i}`.
* `log_rho_unique`: `-x_j ∂_{x_i}` is the only nilpotent endomorphism with `exp = ρ(U_ij)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPoly.PolynomialGLAction (HomogeneousPoly integralAction)

variable {i j : Fin 3}

theorem lieOpH_apply (n : ℕ) (f : HomogeneousPoly n) :
    ((lieOpH n i j f : HomogeneousPoly n) : Poly) = -MvPolynomial.X j * MvPolynomial.pderiv i (f : Poly) := rfl

/-- **`log ρ(U_ij) = -x_j ∂_{x_i}`**: the logarithm series of the unipotent operator `ρ(U_ij)` on `E_n = Sym^n((ℚ³)*)`. -/
theorem log_rho_unipotent (hij : i ≠ j) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((-1 : ℚ) ^ k / (k + 1)) • (integralAction n 0 (unipotentGL i j hij) - 1) ^ (k + 1) =
      lieOpH n i j := by
  rw [rho_unipotent_eq_exp hij n]
  exact log_exp_nilpotent (lieOpH n i j) (n + 1) (lieOpH_pow_succ hij n)

/-- `-x_j ∂_{x_i}` is the unique nilpotent endomorphism of `E_n` whose exponential is `ρ(U_ij)`. -/
theorem log_rho_unique (hij : i ≠ j) (n : ℕ) (D : Module.End ℚ (HomogeneousPoly n)) (hD : IsNilpotent D)
    (h : IsNilpotent.exp D = integralAction n 0 (unipotentGL i j hij)) : D = lieOpH n i j := by
  obtain ⟨N, hN⟩ := hD
  have h1 := log_exp_nilpotent D (max N (n + 1)) (pow_eq_zero_of_le (le_max_left _ _) hN)
  have h2 := log_exp_nilpotent (lieOpH n i j) (max N (n + 1))
    (pow_eq_zero_of_le (le_max_right _ _) (lieOpH_pow_succ hij n))
  rw [h] at h1
  rw [rho_unipotent_eq_exp hij n] at h1
  rw [← h1, h2]

end TernaryPeriodPolynomials.Argument.Identities
