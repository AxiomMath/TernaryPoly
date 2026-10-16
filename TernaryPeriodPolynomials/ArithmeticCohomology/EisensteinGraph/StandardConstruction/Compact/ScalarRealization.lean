module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Admissibility
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RotationTypes
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.Realization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.CommonLevel

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactScalarRealization

theorem principal_eq_reference :
    CuspCommonLevel.principal = TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence := rfl

theorem cuspLift_eq_reference {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (argument : AdelicGL) :
    CuspLift.vector data .plane parameter function induced argument =
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector induced argument := by
  apply data.cusp.injective
  funext binary
  exact (CuspLift.realizes data .plane parameter function induced argument binary).trans
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.realize_planeCuspVector induced argument binary).symm

theorem seminorm_eq_reference (data : CuspidalRepresentation) (vector : data.smooth) :
    CuspRealization.realizationSeminorm data vector =
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector := by
  apply le_antisymm
  · apply (CuspRealization.seminorm_le_iff data vector _
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm_nonneg vector)).mpr
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.realize_le_cuspSupNorm vector
  · apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm_le
    exact CuspRealization.scalar_bound data vector

theorem induced_uniform_binary_bound {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compact, inMaximalCompact compact →
      ∀ binary, ‖data.cusp.realize
        (CuspLift.vector data .plane parameter function induced compact) binary‖ ≤ bound := by
  have stages : TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar.ContinuousStages data.cusp :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes.continuousStages_of_finite_types data.cusp
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointAdmissibility.all_finiteDimensional data)
  obtain ⟨bound, nonnegative, bounded⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar.maximalCompact_bound induced stages
  refine ⟨bound, nonnegative, ?_⟩
  intro compact membership binary
  rw [cuspLift_eq_reference]
  exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.realize_le_cuspSupNorm _ binary).trans
    (bounded compact membership)

theorem flat_uniform_binary_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter compact, inMaximalCompact compact →
      ∀ binary, ‖data.cusp.realize
        (CuspLift.vector data .plane parameter (extension parameter)
          (flat.1 parameter) compact) binary‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := induced_uniform_binary_bound data
    cohomologicalPoint (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter compact membership binary
  rw [CuspLift.flat_vector data extension flat parameter compact membership]
  exact bounded compact membership binary

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactScalarRealization
