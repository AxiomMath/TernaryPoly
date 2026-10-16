module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeSymbolFinal

@[expose] public section


/-!
# Appendix B: the homological Hecke correspondence is the standard Hecke operator

Paper, Appendix B, after `eq:Hecke-formula`: "It remains
to check that this binary correspondence has the standard analytic Hecke normalization on period polynomials. … The
homological correspondence above is the standard Hecke operator on the period polynomial of `h`."

* `homologyHomBridge_holds p d`: the paper's binary homology correspondence `T₂(p)` (the RIGHT correspondence of
  `diag(p,1)` on `H₁(GL₂(ℤ), Sym^d)`, `heckeOp (binDatum p) (binMod d) 1`; see `HeckeHomology/DictionaryDatum.lean`),
  transported to the period space, equals `p^(d+1) • periodHecke d (diag(p,1))`, for every prime `p` and every `d`.
* `homologyPrintedSentence_holds p d hd` (even `d`): for every level-one cusp form `f` of weight `d+2`, the homology
  `T₂(p)` applied to the period polynomial of `f` is the period polynomial of `T_p f`, with the standard analytic Hecke
  operator `T_p` (`BinaryCuspHeckeEndomorphism.T`) and scalar exactly one — the printed sentence, for the paper's
  homology operator.
* `L4_holds`: the degree step of the bridge (the transposed dual lift covers the identity).
* `hecke2_symbolClass_holds`, `hecke2_symbolClass_C1_holds` (unconditional): Hecke equivariance of the binary duality
  `symbolClass` (Lemma B.1's period clause): `T₂(p)(symbolClass Φ) = symbolClass (p^(d+1) • rationalHecke (diag(p,1)) ρ₋₁ Φ)`,
  equivalently with `p⁻¹ • rationalHecke (C1 p) ρ₋₁ Φ`.

The exponent-`+1` Hom-model computations of `Statements.HeckeNormalization` (`homPlus…`, `not_forall_printedClaim…`) are
statements about a different library operator and do not bear on the printed sentence.

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.HeckeBridge

open TernaryPeriodPolynomials.Argument.HeckeNormalization

export TernaryPeriodPolynomials.Argument.HeckeNormalization
  (homologyHomBridge_holds homologyPrintedSentence_holds hecke2_symbolClass_holds hecke2_symbolClass_C1_holds)

export TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeCount (L4_holds)

end TernaryPeriodPolynomials.Argument.Statements.HeckeBridge
