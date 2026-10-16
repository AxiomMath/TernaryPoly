module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Zero.DegreeChainF
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXNonvanishingOfInnerBoundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven

@[expose] public section


/-!
# The good-line cusp residue vanishes unconditionally for `InnerBoundary` classes at `n = 0`

Assembles `ZeroDegreeChainF.phiLZero`/`phiLZero_injective` (the degree-0 reconstruction of
`LocalUniqueness.phiL`/`phiL_injective`, not needing `0 < n`) with
`BridgeXNonvanishingOfInnerBoundary.cuspRes_mem_ML_of_innerBoundary` (the Hecke-free, already
degree-generic membership fact) and `IdentityPlaneEven.arithmeticH1_eq_zero_of_odd` (unconditional
vanishing of `H1` in odd degree) to conclude: at `n = 0`, every `InnerBoundary` line class has zero
good-flag (`v = true`) cusp residue. Exact `n = 0` analogue of
`GoodLineVacuityEven.cuspRes_line_true_eq_zero_of_even`, dropping its `hn`/`heven` (at `n = 0`,
`n + 1 = 1` is odd unconditionally, via `odd_one` rather than `Even.add_one`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneEven (arithmeticH1_eq_zero_of_odd)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Good-line cusp-residue vacuity at `n = 0`.** Exact `n = 0` analogue of
`GoodLineVacuityEven.cuspRes_line_true_eq_zero_of_even`, dropping its `hn`/`heven` (at `n = 0`,
`n + 1 = 1` is odd unconditionally, via `odd_one` rather than `Even.add_one`). -/
theorem cuspRes_line_true_eq_zero_atZero
    {b : StratumH2 0 trivialCharacter .line}
    (inner : InnerBoundary 0 trivialCharacter .line b) :
    cuspRes 0 trivialCharacter .line true b = 0 := by
  have hyM := cuspRes_mem_ML_of_innerBoundary inner
  have h0 : phiLZero ⟨cuspRes 0 trivialCharacter .line true b, hyM⟩ = phiLZero 0 := by
    rw [map_zero]
    exact arithmeticH1_eq_zero_of_odd 1 odd_one 0 _
  exact congrArg Subtype.val (phiLZero_injective h0)

end TernaryPeriodPolynomials.Argument.FacePairing
