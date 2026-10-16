module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Topology
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.RestrictedCountable

@[expose] public section



/-! Second countability of the genuine rational adelic topology. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open IsDedekindDomain
open scoped RestrictedProduct

/-- The actual finite rational places form a countable type. -/
instance finitePlacesCountable : Countable FinitePlace :=
  Rat.HeightOneSpectrum.primesEquiv.injective.countable

/-- Every actual finite rational completion is second countable in its genuine topology. -/
instance finiteCompletionSecondCountable (v : FinitePlace) :
    SecondCountableTopology (v.adicCompletion ℚ) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.secondCountableTopology

/-- The actual finite adele ring is second countable. -/
instance finiteAdelesSecondCountable : SecondCountableTopology FiniteAdeles :=
  restrictedProduct_secondCountable (fun v : FinitePlace => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (fun _ => Valued.isOpen_valuationSubring _)

/-- The full rational adele ring is second countable in the genuine product topology. -/
instance adelesSecondCountable : SecondCountableTopology Adeles :=
  inferInstanceAs (SecondCountableTopology (ℝ × FiniteAdeles))

end GeneralEisenstein.Adelic

end
