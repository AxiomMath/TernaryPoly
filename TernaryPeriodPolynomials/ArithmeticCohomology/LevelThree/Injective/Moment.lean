module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Cocycle
public import Mathlib.Analysis.MellinTransform

@[expose] public section


/-!
# Imaginary-axis moments of level-three cusp forms

For a function `f` on the upper half-plane and `p : ℕ`, the moment
`moment f p = ∫_{t > 0} t^p f(i t) dt` is the Mellin transform of `t ↦ f(i t)` at `p + 1`
(`moment_eq_mellin`). For a cusp form on `Γ₁(3)` these are, up to explicit nonzero constants, the
coefficients of the period polynomial `∫_0^{i∞} f(z) (X₀ - z X₁)^m dz` and the critical values
`Γ(p+1) (2π)^{-p-1} L(f, p + 1)` of the `L`-function.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane MeasureTheory

namespace TernaryPeriodPolynomials.LevelThreeInjective.Moment

/-- The moment `∫_{t > 0} t^p f(i t) dt` of a function on the upper half-plane. -/
def moment (f : ℍ → ℂ) (p : ℕ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ p * f (ofComplex (Complex.I * (t : ℂ)))

/-- The moment is the Mellin transform of `t ↦ f(i t)` at `p + 1`. -/
theorem moment_eq_mellin (f : ℍ → ℂ) (p : ℕ) :
    moment f p = mellin (fun t : ℝ => f (ofComplex (Complex.I * (t : ℂ)))) ((p : ℂ) + 1) := by
  simp only [moment, mellin, add_sub_cancel_right, Complex.cpow_natCast, smul_eq_mul]

end TernaryPeriodPolynomials.LevelThreeInjective.Moment
