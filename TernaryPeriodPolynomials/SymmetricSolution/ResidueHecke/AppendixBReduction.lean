module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Nat

@[expose] public section


/-!
# Lemma B.1 (`lem:literal-residue-comparison`): reduction of the comparison square to the neat-level face evaluation

Formalized by Claude Sonnet 5.5.

What is **proved** (group homology and the Borel-Serre duality of the library; no new geometry):

* `shapiro_inverse_is_corestriction`: the inverse of the Shapiro isomorphism `Sh` is `cor^G_{P_H}` of the summand inclusion;
* `res_H_corestricted_neat`: `res_H` of a corestricted neat class is the `a = 0` residue of the average of the translates of
  the neat Borel-Serre functional on the identity apartment;
* `comparison_square_iff_face_evaluation`: the comparison square
  `PHCompat n` is equivalent to the neat-level identity `FaceEvalAvg n`: `FidL (avg w) = c · edge₂ κ (cor w)` for
  `w ∈ H₃(P_N, 𝓡_{n,H₀})`, `P_N = P_H ∩ Γ(6)`, where `FidL w` is the `a = 0` component of the apartment evaluation of
  `ι_* w ∈ H₃(Γ(6), 𝓡_n)` (the quantity computed by `Lemma33.Retract.FlatIntersectionBridge`).

(the coefficient naturality of the neat duality, `CoefficientNaturality.groupOrdinaryIso_natural`, is proved, so the equivalence
has no hypothesis).

What is **not** proved: `FaceEvalAvg n` itself (the cellular fibre integration of the paper's proof).  It is not an axiom;
it occurs only on one side of the equivalence.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixBReduction

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.IntegralGL3Congruence CategoryTheory
open TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.GroupHomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The inverse of the Shapiro isomorphism is the corestriction of the inclusion of the `H₀`-summand. -/
theorem shapiro_inverse_is_corestriction (n k : ℕ) :
    (shapiroHomologyIso n k).inv = groupHomology.map PH.subtype (lofHom n) k :=
  shapiroHomologyIso_inv n k

/-- `res_H` of a corestriction from `Γ(6)` is the residue of the averaged neat functional on the identity apartment. -/
theorem res_H_corestricted_neat (n : ℕ)
    (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    ((resHLit n ((groupHomology.map PH.subtype (lofHom n) 3).hom
        (corN PN (FibRep n) 3 y)) :
          OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) =
      ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) •
        ∑ q : IntegralGL ⧸ principalSix, termF n y q.out :=
  resHLit_cor_lof n y

/-- **The reduction**: the comparison square of Lemma B.1 is equivalent to the neat-level face evaluation (no
hypothesis: the coefficient naturality of the neat duality is `CoefficientNaturality.groupOrdinaryIso_natural`). -/
theorem comparison_square_iff_face_evaluation (n : ℕ) : PHCompat n ↔ FaceEvalAvg n :=
  phCompat_iff_faceEvalAvg' n

/-- The uniform-in-`n` version. -/
theorem comparison_square_uniform_of_face_evaluation (h : FaceEvalAvgUniform) : PHCompatUniform :=
  phCompatUniform_of_faceEvalAvgUniform' h

/-- The support clause: translates of the neat functional of `ι_* y` by elements outside `P_H · Γ(6)` have zero
`a = 0` residue. -/
theorem face_support_clause (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) {g : IntegralGL}
    (hg : ¬ InPHN g) : termF n y g = 0 :=
  termF_eq_zero n y hg

end TernaryPeriodPolynomials.Argument.Statements.AppendixBReduction
