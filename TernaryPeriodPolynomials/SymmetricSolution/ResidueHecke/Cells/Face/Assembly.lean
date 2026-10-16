module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Nat

@[expose] public section


/-!
# Lemma B.1: assembling `FaceEvalAvg` from a tree parametrization

Formalized by Claude Sonnet 5.5.

`faceEvalAvg_of_data`: suppose the classes of `H₃(P_H, 𝓡_{n,H₀})` are parametrized by a vector space `X` (`yMap` surjective;
this is the Hochschild-Serre/tree parametrization), that `edge₂ κ` of the class parametrized by `x` is `c₁ • ev x`, and that
for every `P_H`-invariant class `w` of `H₃(P_N, 𝓡_{n,H₀})` with `cor w` parametrized by `x`, the apartment residue is
`FidL w = c₂ • ev x`.  Then `FaceEvalAvg n` holds with the constant `c₂ / c₁`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem faceEvalAvg_of_data (n : ℕ) {X : Type} [AddCommGroup X] [Module ℚ X]
    (yMap : X →ₗ[ℚ] groupHomology (FibRep n) 3) (hsurj : Function.Surjective yMap)
    (ev : X →ₗ[ℚ] BinaryV (n + 1)) (c₁ c₂ : ℚ) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hκ : ∀ x, (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (yMap x)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) = c₁ • ev x)
    (hcell : ∀ (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3), avgN PN (FibRep n) 3 w = w →
      ∀ x, yMap x = corN PN (FibRep n) 3 w → FidL n w = c₂ • ev x) :
    FaceEvalAvg n := by
  refine ⟨c₂ / c₁, div_ne_zero hc₂ hc₁, fun w => ?_⟩
  have hidem : avgN PN (FibRep n) 3 (avgN PN (FibRep n) 3 w) = avgN PN (FibRep n) 3 w :=
    avgN_idem (card_ne_zero_gen PN) w
  obtain ⟨x, hx⟩ := hsurj (corN PN (FibRep n) 3 w)
  have hcor : corN PN (FibRep n) 3 (avgN PN (FibRep n) 3 w) = corN PN (FibRep n) 3 w :=
    corN_avgN_gen w
  rw [hcell _ hidem x (hx.trans hcor.symm), ← hx, hκ x, smul_smul, div_mul_cancel₀ _ hc₁]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
