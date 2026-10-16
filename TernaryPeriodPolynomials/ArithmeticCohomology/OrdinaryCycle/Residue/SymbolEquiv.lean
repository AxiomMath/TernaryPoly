module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Equiv

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryResidueSymbol

/-- The actual restriction is onto: the two proved literal reference-period coordinates agree. -/
theorem toBinaryHom_surjective (n : ℕ) : Function.Surjective (toBinaryHom n) := by
  intro f
  refine ⟨(OrdinaryResiduePeriod.periodEquiv n).symm (BinaryModularSymbol.periodEquiv (n+1) f),?_⟩
  apply (BinaryModularSymbol.periodEquiv (n+1)).injective
  change BinaryModularSymbol.periodEvaluation (n+1) (toBinaryHom n _) = _
  rw [BinaryModularSymbol.periodEvaluation_restriction,LinearEquiv.apply_symm_apply]

/-- Literal plane-cone restriction is a linear equivalence of the two actual full integral Hom spaces. -/
def residueSymbolEquiv (n : ℕ) : OrdinaryFullCoefficient.ResidueHom n (-1) ≃ₗ[ℚ]
    BinaryModularSymbol.PeriodHom (n+1) :=
  LinearEquiv.ofBijective (toBinaryHom n) ⟨toBinaryHom_injective n,toBinaryHom_surjective n⟩

@[simp] theorem residueSymbolEquiv_apply (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    residueSymbolEquiv n F = toBinaryHom n F := rfl

/-- Both actual Hom models have precisely the same literal binary period coordinate. -/
theorem residueSymbolEquiv_period (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    BinaryModularSymbol.periodEquiv (n+1) (residueSymbolEquiv n F) = OrdinaryResiduePeriod.periodEquiv n F :=
  BinaryModularSymbol.periodEvaluation_restriction n F

end TernaryPoly.OrdinaryResidueSymbol
