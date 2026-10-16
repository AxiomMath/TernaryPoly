module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Zero
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolRestriction

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryModularSymbol

/-- Actual incidence coning preserves the literal reference period coordinate. -/
theorem periodEvaluation_restriction (n : ℕ)
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    periodEvaluation (n+1) (OrdinaryResidueSymbol.toBinaryHom n F) =
      OrdinaryResiduePeriod.periodEquiv n F := by
  apply Subtype.ext
  exact OrdinaryResidueSymbol.evaluation_toBinaryHom n F

/-- Surjectivity is constructed through actual ordinary cycle functionals and their binary cones. -/
theorem periodEvaluation_surjective (d : ℕ) : Function.Surjective (periodEvaluation d) := by
  cases d with
  | zero =>
    intro q
    exact ⟨0,by rw [map_zero,periodSpace_zero_eq q]⟩
  | succ n =>
    intro q
    refine ⟨OrdinaryResidueSymbol.toBinaryHom n ((OrdinaryResiduePeriod.periodEquiv n).symm q),?_⟩
    rw [periodEvaluation_restriction,LinearEquiv.apply_symm_apply]

/-- The full integral modular-symbol space is literally the homogeneous binary period space.
Generation uses actual Euclidean paths; existence uses the proved ordinary-cycle construction
and actual incidence coning. No presentation or relation-completeness axiom is assumed. -/
def periodEquiv (d : ℕ) : PeriodHom d ≃ₗ[ℚ] OrdinaryResiduePeriod.periodSpace d :=
  LinearEquiv.ofBijective (periodEvaluation d)
    ⟨periodEvaluation_injective d,periodEvaluation_surjective d⟩

@[simp] theorem periodEquiv_apply (d : ℕ) (f : PeriodHom d) :
    (periodEquiv d f).val = f.val reference := rfl

@[simp] theorem periodEquiv_symm_reference (d : ℕ) (q : OrdinaryResiduePeriod.periodSpace d) :
    ((periodEquiv d).symm q).val reference = q.val :=
  congrArg Subtype.val ((periodEquiv d).apply_symm_apply q)

end TernaryPoly.BinaryModularSymbol
