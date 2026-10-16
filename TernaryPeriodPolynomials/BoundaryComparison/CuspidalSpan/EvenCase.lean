module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AutomorphicSpan

@[expose] public section


/-!
# `bad_plane_cuspidal_span`, even case

For even `n > 0` the ambient `H²(Λ₀, Sym^n ⊗ det⁻¹)` at the identity (bad) plane vanishes
entirely (`IdentityPlaneEven.cuspH2_identityPlane_eq_zero`, via the central `-I₂` acting by `-1`
on the odd-degree-coefficient edge target). So the bad-plane Shapiro coordinate of *every* class
is zero, and together with the good-plane coordinate vanishing (`VanishesOnGood`) this forces the
whole class to vanish (`eq_zero_iff_cuspRes`), hence trivially lies in `automorphicPlaneSpan n`.
No use of `InnerBoundary` is needed in this branch.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.IdentityPlaneEven

/-- **Even case of `bad_plane_cuspidal_span`.** For even `n > 0`, every plane class vanishing at
the good plane is already zero (the bad-plane coordinate vanishes unconditionally, since the whole
local cohomology there vanishes for even `n`), hence lies in the span. -/
theorem bad_plane_cuspidal_span_even (n : ℕ) (hn : 0 < n) (heven : Even n)
    (ξ : StratumH2 n trivialCharacter .plane)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ) :
    ξ ∈ automorphicPlaneSpan n := by
  have hg : cuspRes n trivialCharacter .plane true ξ = 0 :=
    (vanishesOnGood_iff_fixedPointH2 ξ).mp hgood (cuspFlag .plane true)
      ((cuspFlag_good_iff .plane true).mpr rfl)
  have hb : cuspRes n trivialCharacter .plane false ξ = 0 :=
    cuspH2_identityPlane_eq_zero n hn heven (cuspRes n trivialCharacter .plane false ξ)
  have hzero : ξ = 0 := (eq_zero_iff_cuspRes .plane ξ).mpr ⟨hg, hb⟩
  rw [hzero]
  exact Submodule.zero_mem _

end TernaryPeriodPolynomials.Argument.CuspidalSpan
