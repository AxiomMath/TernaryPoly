module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HomModel
public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Basic
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodRationalComparison
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenCuspBridge

@[expose] public section


/-!
# Lemma B.1: the composite `edge₂ ∘ κ ∘ Sh` is the odd period polynomial

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3, the last
sentence of `lem:literal-residue-comparison` ("the composite is the usual odd period polynomial").
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.BinaryCuspSymbol TernaryPoly.BinaryCuspPeriod BinaryModularSymbol

theorem edge2_kappa_Sh_val (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    ((edge2 n (kappa n (Sh n F))).val.val : MvPolynomial (Fin 2) ℚ) =
      ((kappa n (Sh n F)).val reference).val := rfl

/-- The residue coordinate `res_H F`, as a rational binary form (the polynomial in `b, c`). -/
theorem resH_extend_val (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    (BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F)).val =
      MvPolynomial.map (algebraMap ℚ ℂ) (resH n F).val.val := rfl

/-- The complexification of the symbol `κ(Sh F)` has the complexified residue polynomial
`res_H F` as its value on the standard edge. -/
theorem complexified_reference (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    (rationalFunctionHom (n + 1) (kappa n (Sh n F))).val reference =
      evaluate (BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F)).val := by
  have e : ((kappa n (Sh n F)).val reference).val = (resH n F).val.val :=
    congrArg (fun x => x.val.val) (residue_comparison_square n F)
  rw [rationalFunctionHom_apply, resH_extend_val, ← rationalEvaluate_map, e]

/-- **The composite is the odd period polynomial.**  If the complexified residue coordinate
`res_H F = edge₂ κ Sh F` is the period `periodMap f` of a cusp form `f`, then the complexified
binary symbol `κ(Sh F)` is the odd cusp symbol of `f`, and its value on the standard edge is the
odd period polynomial of `f` in the same variables `b, c` (`X 0, X 1`). -/
theorem composite_is_odd_period (n : ℕ) (hd : Even (n + 1))
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) (f : Forms (n + 1))
    (h : BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F) = periodMap (n + 1) hd f) :
    rationalFunctionHom (n + 1) (kappa n (Sh n F)) = oddHom f ∧
    (BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F)).val =
      TernaryPeriodPolynomials.Argument.oddPeriodPart (n + 1) f := by
  have h1 : (BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F)).val = oddPeriod f := by
    rw [h]; rfl
  refine ⟨?_, h1.trans (oddPeriod_eq_oddPeriodPart f)⟩
  apply evaluation_injective functionAction
  change (rationalFunctionHom (n + 1) (kappa n (Sh n F))).val reference = (oddHom f).val reference
  rw [complexified_reference, oddHom_reference hd, h1]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
