module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.SwapPolar
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.PolarIntegrability

@[expose] public section


/-! Apply Fubini (`MeasureTheory.setIntegral_prod`) to split the polar-coordinate integral into
an iterated integral over `ρ ∈ Ioi 0` then `θ ∈ Ioo (-π) π`, for clause (iii) of
`real_constant_term_entry` (Appendix C.5). -/


open MeasureTheory Set

namespace TernaryPeriodPolynomials.Argument

/-- Fubini split of `∫ z : ℝ×ℝ, entryIntegrand n z` into an iterated integral over `ρ ∈ Ioi 0`
then `θ ∈ Ioo (-π) π`. -/
theorem entryIntegrand_integral_eq_iterated (n : ℕ) :
    (∫ z : ℝ × ℝ, entryIntegrand n z) =
      ∫ ρ in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ρ • entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ) := by
  rw [entryIntegrand_integral_eq_polar n, polarCoord_target]
  exact MeasureTheory.setIntegral_prod _ (entryIntegrand_polar_integrableOn n)

end TernaryPeriodPolynomials.Argument
