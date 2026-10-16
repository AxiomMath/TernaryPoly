module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.IntegrandPolar
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn

@[expose] public section


/-! The measure-theoretic polar change of variables for `∫ z : ℝ×ℝ, entryIntegrand n z`: swap the
coordinates (a no-op on the integral since both marginals are `volume`), then apply
`integral_comp_polarCoord_symm`, landing on the pointwise polar rewrite from `IntegrandPolar.lean`.
Used for clause (iii) of `real_constant_term_entry` (Appendix C.5). -/


namespace TernaryPeriodPolynomials.Argument

open MeasureTheory

/-- Swapping coordinates is a no-op on `∫ z : ℝ×ℝ, entryIntegrand n z`, since both marginal
measures are `volume`. -/
theorem entryIntegrand_integral_swap (n : ℕ) :
    (∫ z : ℝ × ℝ, entryIntegrand n z) = ∫ z : ℝ × ℝ, entryIntegrand n z.swap :=
  (MeasureTheory.integral_prod_swap (entryIntegrand n)).symm

/-- The polar rewrite of `∫ z : ℝ×ℝ, entryIntegrand n z.swap` via `integral_comp_polarCoord_symm`:
at `p = (ρ,θ)` the swapped point `(polarCoord.symm p).swap` is `(ρ sin θ, ρ cos θ)`. -/
theorem entryIntegrand_integral_eq_polar (n : ℕ) :
    (∫ z : ℝ × ℝ, entryIntegrand n z) =
      ∫ p in polarCoord.target,
        p.1 • entryIntegrand n (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
  rw [entryIntegrand_integral_swap n,
    ← integral_comp_polarCoord_symm (fun z : ℝ × ℝ => entryIntegrand n z.swap)]
  congr 1

end TernaryPeriodPolynomials.Argument
