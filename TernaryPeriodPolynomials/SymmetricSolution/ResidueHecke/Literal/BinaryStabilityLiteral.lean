module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.BinaryStability
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Assembly
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.MapsMain

@[expose] public section


/-!
# Lemma 4.5: unconditional binary Hecke stability of `𝓛_n` on literal homology

Formalized by Claude Sonnet 5.5.
Paper: Lemma 4.5 (`lem:residue-period`), proof.

Instantiates `BinaryStability.LnHom_binary_stable` with `phCompat_literal` (Lemma B.1, the residue comparison square
`edge₂ ∘ κ ∘ Sh = c · res_H`) and `hecke_formula_literal` (`eq:Hecke-formula`, `T₃(p,1) = p T₂(p) + p² I`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma45Literal

open TernaryPeriodPolynomials.Argument.AppendixBResidue TernaryPeriodPolynomials.Argument.HeckeHomology

/-- `eq:Hecke-formula` is `HeckeFormula`. -/
theorem heckeFormula_literal (p : ℕ) [Fact p.Prime] (n : ℕ) : HeckeFormula p n :=
  fun y => hecke_formula_literal p n y

/-- **Lemma 4.5, Hecke stability under the binary operator**, unconditional on literal homology. -/
theorem LnHom_binary_stable_literal (p : ℕ) [Fact p.Prime] (n : ℕ)
    (q : TernaryPoly.OrdinaryResiduePeriod.periodSpace (n + 1)) (hq : q ∈ LnHom n) : T2B p n q ∈ LnHom n :=
  LnHom_binary_stable p n (phCompat_literal n) (heckeFormula_literal p n) q hq

end TernaryPeriodPolynomials.Argument.Lemma45Literal
