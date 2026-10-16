module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Clause3

@[expose] public section


/-!
# The antiholomorphic real entry: the conjugate component has the conjugate scalar

Paper: Appendix C.5, ("The conjugate component
has the conjugate scalar") and ("the holomorphic and antiholomorphic scalars are complex conjugates,
`-2πi/(n+1)` and `2πi/(n+1)`").

The antiholomorphic seed is, by definition, the complex conjugate of the holomorphic one, "including the
coefficient polynomial and differential". On the local lowest-weight datum `h(τ) = (τ+i)^{-k}` of the real entry its
integrand is therefore `r⁻³ (τ̄ - i)^{-k} b̄ⁿ`, and the corresponding value at `τ = i` is `(-1)ⁿ(-2i)^{-k}`.

* `entryIntegrandBar`, `entryIntegralBar`: the antiholomorphic integrand and the integral `I̅_n = +i ∫ r⁻³ (τ̄ - i)^{-k} b̄ⁿ ds dt`.
* `entryIntegrandBar_eq_conj`, `entryIntegralBar_eq_conj`: the integrand and the integral are the complex conjugates of the
  holomorphic ones.
* `real_entry_conjugate`: the antiholomorphic scalar `I̅_n / ((-1)ⁿ(-2i)^{-(n+3)})` is `2πi/(n+1)`, the complex conjugate of
  `c_∞ = -2πi/(n+1)`, equal to `-c_∞`, and nonzero.

Formalized by Claude Sonnet 5.5.
-/


open MeasureTheory ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument

/-- The antiholomorphic integrand `r⁻³ (τ̄ - i)^{-(n+3)} b̄ⁿ`: the conjugate of `entryIntegrand`, written out. -/
def entryIntegrandBar (n : ℕ) (st : ℝ × ℝ) : ℂ :=
  (entryRadius st : ℂ) ^ (-3 : ℤ) * (conj (entryTau st) - Complex.I) ^ (-((n : ℤ) + 3)) *
    conj (entryCoefficient st) ^ n

/-- The antiholomorphic real integral `I̅_n = +i ∫_{ℝ²} r⁻³ (τ̄ - i)^{-k} b̄ⁿ ds dt` (the conjugate of `-i`
in `entryIntegral` is `+i`). -/
def entryIntegralBar (n : ℕ) : ℂ :=
  Complex.I * ∫ st : ℝ × ℝ, entryIntegrandBar n st

theorem entryIntegrandBar_eq_conj (n : ℕ) (st : ℝ × ℝ) :
    entryIntegrandBar n st = conj (entryIntegrand n st) := by
  unfold entryIntegrandBar entryIntegrand
  simp only [map_mul, map_zpow₀, map_pow, map_add, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]

theorem entryIntegralBar_eq_conj (n : ℕ) : entryIntegralBar n = conj (entryIntegral n) := by
  unfold entryIntegralBar entryIntegral
  simp_rw [entryIntegrandBar_eq_conj]
  rw [integral_conj, map_mul, map_neg, Complex.conj_I, neg_neg]

theorem conj_entryNormalization (n : ℕ) :
    conj ((-1 : ℂ) ^ n * (2 * Complex.I) ^ (-((n : ℤ) + 3))) =
      (-1 : ℂ) ^ n * (-2 * Complex.I) ^ (-((n : ℤ) + 3)) := by
  simp only [map_mul, map_zpow₀, map_pow, map_neg, map_one, map_ofNat, Complex.conj_I]
  congr 2
  ring

/-- **The antiholomorphic real entry.** The antiholomorphic integrand and integral are the
complex conjugates of the holomorphic ones; dividing `I̅_n` by the conjugate `(-1)ⁿ(-2i)^{-(n+3)}` of the value at `τ = i`
gives `2πi/(n+1)`, which is the complex conjugate of `c_∞ = -2πi/(n+1)`, equals `-c_∞`, and is nonzero. -/
theorem real_entry_conjugate (n : ℕ) :
    (∀ st : ℝ × ℝ, entryIntegrandBar n st = conj (entryIntegrand n st)) ∧
    entryIntegralBar n = conj (entryIntegral n) ∧
    entryIntegralBar n / ((-1) ^ n * (-2 * Complex.I) ^ (-((n : ℤ) + 3))) =
      2 * Real.pi * Complex.I / ((n : ℂ) + 1) ∧
    2 * Real.pi * Complex.I / ((n : ℂ) + 1) = conj (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) ∧
    2 * Real.pi * Complex.I / ((n : ℂ) + 1) = -(-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) ∧
    2 * Real.pi * Complex.I / ((n : ℂ) + 1) ≠ 0 := by
  have hc : conj (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) =
      2 * Real.pi * Complex.I / ((n : ℂ) + 1) := by
    simp only [map_div₀, map_mul, map_neg, map_add, map_one, map_natCast, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast this
  refine ⟨entryIntegrandBar_eq_conj n, entryIntegralBar_eq_conj n, ?_, hc.symm, ?_, ?_⟩
  · rw [← conj_entryNormalization, entryIntegralBar_eq_conj, ← map_div₀,
      real_constant_term_entry_clause3 n, hc]
  · ring
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hn

end TernaryPeriodPolynomials.Argument

end
