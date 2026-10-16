module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Main

@[expose] public section


/-!
# the canonical face pairing has the cup-form property

Formalized by Claude Sonnet 5.5.

`isCupPairing_facePairingCan`: `facePairingCan` (the cup-form normalised pairing of `𝒞(H¹(N_R, E))` and `𝒞(H¹(N_R, E^*))`) satisfies `IsCupPairing` for the Levi-invariant Koszul pairing,
so `cuspidal_pairing_ind` applies to it at both levels.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped Classical

variable {N : ℕ}

theorem isCupPairing_facePairingCan (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep]
    [FiniteDimensional ℂ (splitRadicalH1Representation s rep)]
    [FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep))] :
    IsCupPairing hN (splitRadicalH1Representation s rep) (splitRadicalH1Representation s (dualRepG rep))
      (radPairingOf (ext := ext) (perfectInv_dual rep))
      (fun γ x y => radPairingOf_levi (perfectInv_dual rep) s γ (hdet γ) x y)
      (fun x hx => radPairingOf_left (perfectInv_dual rep) x hx) (fun y hy => radPairingOf_right (perfectInv_dual rep) y hy)
      (facePairingCan hN s hdet rep) :=
  fun Φ Φ' h0 _ => facePairingCan_cup hN s hdet rep Φ Φ' h0

end TernaryPeriodPolynomials.Argument.CuspidalInduction
