module

public import TernaryPeriodPolynomials.BoundaryComparison.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Final

@[expose] public section


/-! Target: the plane coordinates of `L Lᵀ` and the tangent entry `ar:eq:tangententry` of
Appendix C.5. -/

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Appendix C.5, coordinates and tangent entry.** For `L = w₀⁻¹ u(s,t)`, the Gram matrix
`L Lᵀ` has plane coordinates `u = (s,t)/r²` and `τ = (-st + ir)/(1+s²)`; along the
tangent matrices `v₂ = E₁₃` and `x₀ = E₂₃` one has `dτ(x₀) = s dτ(v₂) + 1`,
`β(x₀) = s β(v₂) + t/r²`, and `(β ∧ dτ)(v₂, x₀) = -i/r³`. -/
theorem real_entry_tangent (s t : ℝ) :
    gramPlaneU (entryCurve s t 0 0) = (s / entryRadius (s, t) ^ 2, t / entryRadius (s, t) ^ 2) ∧
    gramPlaneTau (entryCurve s t 0 0) = entryTau (s, t) ∧
    entryDTau s t (Matrix.single 1 2 1) = s * entryDTau s t (Matrix.single 0 2 1) + 1 ∧
    entryBeta s t (Matrix.single 1 2 1) =
      s * entryBeta s t (Matrix.single 0 2 1) + ((t / entryRadius (s, t) ^ 2 : ℝ) : ℂ) ∧
    entryBeta s t (Matrix.single 0 2 1) * entryDTau s t (Matrix.single 1 2 1) -
        entryBeta s t (Matrix.single 1 2 1) * entryDTau s t (Matrix.single 0 2 1) =
      -Complex.I / (entryRadius (s, t) : ℂ) ^ 3 := by
  exact real_entry_tangent_proved s t

end TernaryPeriodPolynomials
