module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Cusps
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Bridge

@[expose] public section


open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# The dual series for `Γ(N)` and the dual constant terms from the plane statements

Formalized by Claude Sonnet 5.5.

`dualSeriesClass_gammaN` is the class of `ȷ̃^* ℰ_P(ω_f)` in `H²(Γ(N), E^∨)` (`ℰ_Q^∨` for the seed of `f`);
`dualSeriesClass_gammaN_eq : = jPull (eisensteinClass_gammaN …)`; `dual_constant_terms_series`: the plane statements
`ConstantTermsAt` for `ℰ_P(ω_f)` imply those for the dual series.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPoly.SmoothLocalDeRham

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **The dual series `ℰ_Q^∨` for `Γ(N)`**: the class in `H²(Γ(N), E^∨)` of the closed form `ȷ̃^* ℰ_P(ω_f)`. -/
def dualSeriesClass_gammaN : groupCohomology.H2 (Rep.of (dualRhoN N n)) :=
  dualSeriesClass (gammaN N) (gammaN N) (jN N) (fun _ => rfl) (leviGroup N) n f hn (leviIn_gammaN N)

theorem dualSeriesClass_gammaN_eq :
    dualSeriesClass_gammaN N n f hn = jPull N n (eisensteinClass_gammaN N n f hn) :=
  dualSeriesClass_eq (gammaN N) (gammaN N) (jN N) (fun _ => rfl) (leviGroup N) n f hn (leviIn_gammaN N)

/-- **`eq:dualconstantterms` from the plane statements for `ℰ_P`** (the transport theorem for the actual series of `Γ(N)`). -/
theorem dual_constant_terms_series
    (ξ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp
      (Subgroup.inclusion (gammaNPAt_le N h)))))
    (ζ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp
      (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (H : ConstantTermsAt N n (gammaRho (gammaN N) n) (eisensteinClass_gammaN N n f hn) ξ' ζ') :
    ConstantTermsAt N n (dualRhoN N n) (dualSeriesClass_gammaN N n f hn)
      (fun h => pullPQ N n h (ζ' (jmath h))) (fun h => pullQP N n h (ξ' (jmath h))) := by
  rw [dualSeriesClass_gammaN_eq]
  exact dual_constant_terms_transport _ ξ' ζ' H

end TernaryPeriodPolynomials.Argument.EisensteinDual
