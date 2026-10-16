module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Cup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Coefficients

@[expose] public section


/-!
# The model coefficient pairing is the rational pairing of a representation with its contragredient

The pairing `T.B` of the duality data `dualityData n χ`
(`TraceRepresentatives`), taken pointwise in `ModelCup.Bhom`, is on the complexification of the rational homogeneous
polynomials the extension of scalars of the rational form `BQ` (`Coefficients.dualPairing_complexify`), which is
non-degenerate and identifies the rational representation `VQ n` twisted by the involution `φ` with its contragredient:
`Coefficients.dualEquiv`, `dualEquiv_equivariant`, `dualRep_comparison`, `dualValue_dualRepresentation`.  So the model
cone cup product with coefficient pairing `Bhom` on `E ⊗ E^φ`, restricted to rational classes, is the cone cup product
for the evaluation pairing `E ⊗ E^∨ → ℚ` of a rational representation with its library contragredient
(`dualRepresentation`), up to the extension of scalars `ℚ → ℂ`.  The statements here record the pairing identity and
that the model `φ`-twist is the contragredient on the rational structure.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- The model coefficient pairing of `dualityData` is, on rational vectors, the rational form `BQ`. -/
theorem Bhom_complexify (n : ℕ) (χ : RankOneCharacter) (v w : VQ n) :
    Bhom (dualityData n χ) (complexify n v) (complexify n w) = ((BQ n v w : ℚ) : ℂ) :=
  dualPairing_complexify n v w

/-- Under the rational form `BQ`, the rational polynomials correspond to their contragredient, equivariantly for
the `φ`-twisted action on the model side and the contragredient action of the rational dual. -/
theorem BQ_eq_dualEquiv (n : ℕ) (v w : VQ n) : BQ n v w = dualEquiv n v w := rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
