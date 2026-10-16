module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.GammaNTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.TreeCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Duality
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalCriterion

@[expose] public section


/-!
# Finite-dimensionality of the cuspidal groups of `Γ(N)`

Formalized by Claude Sonnet 5.5.

`finiteDimensional_H1_gammaNGL`: for `N ≥ 3` and a finite-dimensional `A`, `H¹(gammaNGL N, A)` is finite-dimensional (the dual Farey tree computes it: `cohIso`, `c1_finite`).
`finiteDimensional_cuspidal`: the cuspidal group `cuspidalSubspace (Γ(N)) V` of Mathlib's `Γ(N)` is finite-dimensional for finite-dimensional `V` (`cuspEquiv`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open CongruenceSubgroup

variable {N : ℕ}

theorem finiteDimensional_H1_gammaNGL (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (groupCohomology.H1 A) := by
  have := c1_finite (ρ := A.ρ) (gammaNFareyData hN)
  exact LinearEquiv.finiteDimensional (cohIso A (gammaNFareyData hN))

/-- **The cuspidal group of `Γ(N)` with finite-dimensional coefficients is finite-dimensional.** -/
theorem finiteDimensional_cuspidal (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (cuspidalSubspace (Gamma N) V) := by
  have h1 : FiniteDimensional ℂ (transRep hN V) := inferInstanceAs (FiniteDimensional ℂ V)
  have h2 := finiteDimensional_H1_gammaNGL hN (transRep hN V)
  have h3 : FiniteDimensional ℂ (cuspidalSub (transRep hN V)) := inferInstance
  exact LinearEquiv.finiteDimensional (cuspEquiv hN V).symm

end TernaryPeriodPolynomials.Argument.FaceDescent
