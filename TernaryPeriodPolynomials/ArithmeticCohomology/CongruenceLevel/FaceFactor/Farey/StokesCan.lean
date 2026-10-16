module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.StokesCup
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FaceCanonical

@[expose] public section


/-!
# The canonical face pairing in cusp form

Formalized by Claude Sonnet 5.5.

`facePairingCan_eq_cusp_sum`: on the classes of normalised twisted cusp functions `Φ`, `Φ'` (with values in the Levi modules `H¹(R, E)`, `H¹(R, E^*)` of a face), the canonical face pairing is
`2 ∑_c ( ⟨Φ(c), g(σ_c)⟩_Kos + η(σ_c) )` where `g = coc G'` is the cocycle carrying `Φ'`, `⟨ , ⟩_Kos = leviCoupling` and `η` is any primitive of the cup cocycle `⟨f x, x g y⟩`.
So the right-hand side of the fibre-integration identity M3 is a sum over the cusp orbits of a local term plus a primitive of the base cup cocycle.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open CongruenceSubgroup
open scoped Classical

variable {N : ℕ}

theorem facePairingCan_eq_cusp_sum (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep]
    (Φ : Tw (transRep hN (splitRadicalH1Representation s rep)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation s (dualRepG rep))).ρ) (h0 : Φ.1 cusp1 = 0)
    (η : gammaNGL N → ℂ)
    (hη : ∀ x y, η (x * y) = η x + η y -
      (leviCoupling hN s hdet rep).e (fTw (transRep hN (splitRadicalH1Representation s rep)) Φ.1 x)
        ((transRep hN (splitRadicalH1Representation s (dualRepG rep))).ρ x
          (coc (transRep hN (splitRadicalH1Representation s (dualRepG rep))).ρ (cuspG hN Φ'.2) y))) :
    facePairingCan hN s hdet rep
        ((cuspEquiv hN (splitRadicalH1Representation s rep)).symm ⟨mTw _ Φ, mTw_mem_cuspidal _ Φ⟩)
        ((cuspEquiv hN (splitRadicalH1Representation s (dualRepG rep))).symm ⟨mTw _ Φ', mTw_mem_cuspidal _ Φ'⟩) =
      2 * ∑ c ∈ (cuspReps hN).R, ((leviCoupling hN s hdet rep).e (Φ.1 c)
        (coc (transRep hN (splitRadicalH1Representation s (dualRepG rep))).ρ (cuspG hN Φ'.2) (cuspSigma c)) + η (cuspSigma c)) := by
  rw [facePairingCan_cup hN s hdet rep Φ Φ' h0]
  exact cupForm_eq_cusp_sum hN (leviCoupling hN s hdet rep) Φ.2 Φ'.2 η hη

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
