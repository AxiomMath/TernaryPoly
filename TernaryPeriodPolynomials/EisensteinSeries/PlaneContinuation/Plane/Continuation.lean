module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RecoveredAlgebraCombination
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MeromorphicRecoveryAlgebra

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneContinuation

theorem exists_continuation {degree : ℕ} {data : InducingData degree} {original : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data original) :
    ∃ continuation : ℂ → AdelicGL → ℂ, IsEisensteinContinuation original continuation := by
  let basis := Module.finBasis ℂ (RecoveryTupleAlgebra.algebra data)
  obtain ⟨coefficients, cutoff, bound, meromorphic, inverse⟩ :=
    MeromorphicRecoveryAlgebra.exists_inverse_coefficients data basis
  choose families familiesFlat realizations using fun index =>
    FlatAlgebraRealization.exists_flat flat (basis index)
  obtain ⟨continuation, continues⟩ :=
    RecoveredAlgebraCombination.exists_continuation familiesFlat coefficients meromorphic
  refine ⟨continuation, ContinuationAlgebra.transfer continues cutoff ?_⟩
  intro parameter above point
  exact congrFun (RecoveredAlgebraCombination.eq_original flat familiesFlat (fun index => basis index)
    coefficients realizations parameter (lt_trans bound above)
    (inverse ⟨parameter, lt_trans bound above⟩ above.le).1) point

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneContinuation
