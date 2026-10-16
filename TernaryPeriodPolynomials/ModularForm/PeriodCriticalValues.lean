module

public import TernaryPeriodPolynomials.ModularForm.CriticalValues.Mellin
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.EvenPeriodMembership
public import TernaryPeriodPolynomials.ModularForm.PeriodIntegral

@[expose] public section


/-!
# Critical `L`-values and the coefficients of the period polynomial (Sections 6-7)

Formalized by Claude Sonnet 5.5.

**New** (`Proofs/CriticalValues/Mellin.lean`): the Mellin identity at *every* critical integer
(`periodMoment_eq_completedL`, `axis_integral_eq`), the literal `eq:period-critical-coefficients` (`periodPolynomial_eq_critical`), the parts in `X`
(`evenPeriodPart_eq_critical`, `oddPeriodPart_eq_critical`), the functional equation and the axis identity of the critical values.

**Cited, already in the library**:
* `TernaryPoly.BinaryCuspPeriod.moment_nat_eq`, `lseries_eq_L` are the single points `s = d`; the all-`s` version is `moment_eq_gamma_mul_L`;
* `Argument.Statements.PeriodIntegral.periodPolynomial_eval_eq_integral`: `r_h(x,y) = ∫₀^{i∞} h(τ)(τy - x)^n dτ`;
* axis normalization: `TernaryPeriodPolynomials.Argument.Corollary14.normalizedEvenPeriodPart_axis_first`, `…_axis_second`, `…_mem_evenPeriodSpace` (all even `n ≠ 0`; the homogeneity
  `TernaryPeriodPolynomials.Argument.CuspForms.normalizedEvenPeriodPart_isHomogeneous`); the identity behind it is `axis_identity` below;
* the dimension calculation of the proof of `cor:dimensions` (Eichler-Shimura isomorphisms `S_{n+2} ≅ W_n^{sym}, W_n^{alt}`, vanishing in degree zero and
  odd degree, the Hilbert series `2t¹⁰/((1-t⁴)(1-t⁶))`) is the target `period_isomorphisms_and_finrank` (proved, `TernaryPeriodPolynomials.Argument.Corollary14.corollary_1_4_assembly`) and
  `Argument.Statements.corollary_1_4_general`.
* `lSeries_outer_critical_ne_zero` (nonvanishing of the outer values `L(h,k-2)`, `L(h,k-1)`), `Argument.Statements.AlternatingEven` (Proposition 5.1).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.PeriodCriticalValues

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.CriticalValues

alias mellin_gamma_L := moment_eq_gamma_mul_L
alias period_moment_eq_completed_L := periodMoment_eq_completedL
alias period_critical_coefficients := periodPolynomial_eq_critical
alias completed_L_reflection := completedL_reflection
alias period_axis_identity := axis_identity

open MvPolynomial in
/-- **`eq:period-critical-coefficients` with its analytic content**. For `h ∈ S_{n+2}`: (a) the period polynomial has the printed
coefficients `(-1)^{n-j} binom(n,j) i^{j+1} Λ(h,j+1)`; (b) `∫₀^{i∞} h(τ) τ^j dτ = i^{j+1} Γ(j+1) (2π)^{-j-1} L(h,j+1)` for every `j`; (c) the evaluation
`r_h(x,y) = ∫₀^{i∞} h(τ)(τy - x)^n dτ`; (d) `Λ(h, n+1-j) = i^{n+2} Λ(h,j+1)`. -/
theorem period_critical_values (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) :
    periodPolynomial n h = ∑ j ∈ Finset.range (n + 1),
      C ((-1) ^ (n - j) * (n.choose j : ℂ) * Complex.I ^ (j + 1) * completedL n h ((j + 1 : ℕ) : ℂ)) *
        X 0 ^ (n - j) * X 1 ^ j ∧
    (∀ j : ℕ, ∫ t : ℝ in Set.Ioi 0, h (UpperHalfPlane.ofComplex (Complex.I * t)) * (Complex.I * (t : ℂ)) ^ j * Complex.I =
      Complex.I ^ (j + 1) * ((Real.pi : ℂ) * 2) ^ (-((j + 1 : ℕ) : ℂ)) * Complex.Gamma ((j + 1 : ℕ) : ℂ) *
        ModularForm.L (TernaryPoly.BinaryCuspPeriod.weight_pos n) h ((j + 1 : ℕ) : ℂ)) ∧
    (∀ x y : ℂ, eval ![x, y] (periodPolynomial n h) =
      ∫ t : ℝ in Set.Ioi 0, h (UpperHalfPlane.ofComplex (Complex.I * t)) * (Complex.I * t * y - x) ^ n *
        Complex.I) ∧
    (∀ j : ℕ, j ≤ n → completedL n h ((j + 1 : ℕ) : ℂ) =
      Complex.I ^ (n + 2) * completedL n h ((n - j + 1 : ℕ) : ℂ)) := by
  refine ⟨periodPolynomial_eq_critical n h, fun j => ?_, fun x y => ?_, fun j hj => completedL_reflection n h hj⟩
  · rw [axis_integral_eq n h j, completedL, mul_comm (Real.pi : ℂ) 2]
    ring
  · exact Statements.PeriodIntegral.periodPolynomial_eval_eq_integral n h x y

end TernaryPeriodPolynomials.Argument.Statements.PeriodCriticalValues
