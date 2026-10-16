module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobeniusData
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobeniusL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeDegreeCount

@[expose] public section


/-!
# The Hecke bridge, unconditionally

Formalized by Claude Sonnet 5.5.

Combines the five interface statements `L1` (Frobenius duality), `L2` (transposition), `L3` (dual lift),
`L4` (the transposed lift covers the identity, S5: `BridgeDegreeCount.L4_holds`) and `L5` (Frobenius-form Hecke formula)
with the bookkeeping `bridge_of_interfaces` of `BridgeMain.lean`.  The paper's homology operator
`heckeOp (binDatum p) (binMod d) 1`, transported to the period space, is exactly `p^(d+1) • periodHecke d (diag(p,1))`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

/-- **The bridge `H-1`** (all primes `p`, all degrees `d`): `T₂(p) = p^(d+1) · periodHecke d (diag(p,1))` on the period space. -/
theorem homologyHomBridge_holds (p d : ℕ) [Fact p.Prime] : HomologyHomBridge p d ((p : ℚ) ^ (d + 1)) :=
  bridge_of_interfaces p d (L1_holds d) (L2_holds p) (L3_holds p) (BridgeDegreeCount.L4_holds) (L5_holds p d)

/-- **The printed sentence for the homology operator** (even `d`): the paper's `T₂(p)` is the standard Hecke operator. -/
theorem homologyPrintedSentence_holds (p d : ℕ) [Fact p.Prime] (hd : Even d) : HomologyPrintedSentence p d hd :=
  homologyPrintedSentence_of_bridge hd (homologyHomBridge_holds p d)

end TernaryPeriodPolynomials.Argument.HeckeNormalization
