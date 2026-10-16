module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineLocalOp

@[expose] public section


/-!
# `psiL` of a cusp-residue is the direct good-line fixed-point reduction (M1a, reconciliation)

`psiL` (`GoodLineLocalOp.lean`) is defined as `stabilizerTransportH2` transporting along `gammaL`
from the reference cusp flag `cuspFlag .line true` to `mk rationalGoodLine`. `cuspRes`
(`CuspReduction.lean`) is literally `fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
(cuspFlag side good)`. Composing them is therefore exactly the hypothesis pattern of
`stabilizerTransportH2_fixedPointH2` (`StabilizerTransport.lean`), which identifies a transported
fixed-point reduction at the source with the direct fixed-point reduction at the target. This
removes the need to go through the cusp flag at all: `psiL n` applied to the cusp-residue of a
stratum class equals the direct restriction of that class to the good-line stabilizer `Λ₁`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Reconciliation.** Transporting the cusp-residue of a `.line`-side stratum class along `psiL`
is the same as restricting the class directly to the good-line stabilizer `Λ₁`. -/
theorem psiL_cuspRes_eq (n : ℕ) (coordinate : StratumH2 n trivialCharacter .line) :
    psiL n (cuspRes n trivialCharacter .line true coordinate) =
      fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
        coordinate :=
  stabilizerTransportH2_fixedPointH2 rationalLevel (ρn n) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul coordinate

end TernaryPeriodPolynomials.Argument.FacePairing
