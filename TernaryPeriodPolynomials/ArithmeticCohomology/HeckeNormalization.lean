module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFinal

@[expose] public section


/-!
# The Appendix B "standard analytic Hecke normalization" sentence

Formalized by Claude Sonnet 5.5.

Export of `TernaryPeriodPolynomials.Argument.HeckeNormalization.{Scalar, Eigenperiod, Refutation, Bridge}`.  Paper
the paper: "It remains to check that this binary correspondence
has the standard analytic Hecke normalization on period polynomials. ... The homological correspondence above is
the standard Hecke operator on the period polynomial of `h`."

* The two displayed identities and the weight `d + 2` transformation of the differential are proved in
  `Statements.AnalyticPeriodHecke` (not repeated here).
* **Library Hom model, exponent `+1`** (a choice of rational extension `det^e`, `e = +1 = -1 + 2`, of the
  integral coefficient system; NOT identified with the paper's homology operator): proved unconditionally
  `homPlusComplexHecke p ∘ periodMap = p^{1-d} • periodMap ∘ T_p` (`homPlus_periodMap_zpow`), hence the sentence
  fails in that model (`printedClaim_iff`, `not_forall_printedClaim_weight24`), and Lemma 4.5's vanishing is
  insensitive to the scalar (`homPlus_intertwines`, `stable_extreme_kernel_eq_bot_homPlus`,
  `actualLiftable_complex_eq_bot_homPlus`).
* **The paper's homology operator** `T₂(p) = heckeOp (binDatum p) (binMod d) 1` (the `hecke2`): the
  bridge `HomologyHomBridge p d (p^(d+1))` (H-1, `homologyT2 p d = p^(d+1) • periodHecke d (diag(p,1))`) is PROVED for
  every prime `p` and every `d` (`homologyHomBridge_holds`), and therefore, for even `d`, the printed sentence
  `HomologyPrintedSentence p d hd` (H-2: `T₂(p) (periodMap f) = periodMap (T_p f)` for every level-one cusp form of
  weight `d + 2`) holds with scalar exactly `1` (`homologyPrintedSentence_holds`).  The proof is the assembly
  `bridge_of_interfaces` of the five interface statements `L1 d` (Frobenius duality), `L2 p` (transposition),
  `L3 p` (dual lift), `L4 p` (the transposed lift covers the identity, S5: `BridgeDegreeCount.L4_holds`) and
  `L5 p d` (Frobenius-form Hecke formula).  Only `propext`, `Classical.choice`, `Quot.sound`.
  The Hom-model refutation above concerns a different operator and is not in tension with this.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.HeckeNormalization

open TernaryPeriodPolynomials.Argument.HeckeNormalization

export TernaryPeriodPolynomials.Argument.HeckeNormalization
  (homPlusRationalHecke homPlusRationalHecke_spec homPlusComplexHecke homPlusComplexHecke_eq
    periodMap_homPlus homPlus_periodMap_zpow homPlus_weight12_prime2
    homPlus_intertwines stable_extreme_kernel_eq_bot_homPlus actualLiftable_complex_stable_homPlus
    actualLiftable_complex_eq_bot_homPlus
    HomModelPrintedClaim printedClaim_iff not_forall_printedClaim not_forall_printedClaim_weight24
    homologyT2 HomologyHomBridge HomologyPrintedSentence homologyComplexT2_of_bridge
    homology_periodMap_of_bridge homology_printed_sentence_of_bridge homologyPrintedSentence_of_bridge
    bridge_scalar_of_printed_sentence)

export TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
  (L1 L2 L3 L4 L5 bridge_of_interfaces printed_sentence_of_interfaces homT_eq descend)

export TernaryPeriodPolynomials.Argument.HeckeNormalization
  (homologyHomBridge_holds homologyPrintedSentence_holds)

export TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeCount (L4_holds)

end TernaryPeriodPolynomials.Argument.Statements.HeckeNormalization
