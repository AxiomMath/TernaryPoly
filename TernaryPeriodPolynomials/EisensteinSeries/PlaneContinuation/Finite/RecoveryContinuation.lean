module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RecoveryIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ConstantRealMass

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryContinuation

theorem exists_recovery {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation (fun parameter point => sectionFunction (flat.1 parameter) point) continuation ∧
      (∀ point parameter, MeromorphicAt (fun parameter => average (continuation parameter) point) parameter) ∧
      (∀ point parameter, Integrable (fun pair : Adeles × Adeles =>
        continuation parameter (planeUnipotent pair.1 pair.2 * point)) parameterMeasure) ∧
      ∀ point parameter, (1 - (degree : ℝ)) / 2 < parameter.re →
        average (continuation parameter) point = sectionFunction (flat.1 parameter) point := by
  obtain ⟨cutoff, smooth, compact, supported, nonzero, mass⟩ := ConstantRealMass.exists_cutoff
  obtain ⟨continuation, continues, meromorphic, integrable, recovery, _⟩ :=
    LinearProfileRecovery.exists_recovery flat cutoff smooth compact supported
  let coefficient : ℂ := (ConstantRealMass.baseMass cutoff)⁻¹
  have sectionEquality : (fun parameter point => coefficient *
      VectorGodement.sectionFunction data (LinearProfileRecovery.test (flat.1 parameter) cutoff) parameter point) =
        fun parameter point => sectionFunction (flat.1 parameter) point := by
    funext parameter point
    have value := (section_eq (flat.1 parameter) cutoff point).trans
      (congrArg (fun scalar : ℂ => scalar * sectionFunction (flat.1 parameter) point) (mass point))
    exact (congrArg (fun scalar : ℂ => coefficient * scalar) value).trans (inv_mul_cancel_left₀ nonzero _)
  refine ⟨fun parameter point => coefficient * continuation parameter point, ?_, ?_, ?_, ?_⟩
  · have result := ContinuationAlgebra.multiply continues (fun _ => coefficient)
      (fun parameter => MeromorphicAt.const coefficient parameter)
    exact sectionEquality ▸ result
  · intro point parameter
    have result := (MeromorphicAt.const coefficient parameter).mul (meromorphic point parameter)
    simpa only [Pi.mul_def, PlaneConstantTerm.average, integral_const_mul] using result
  · intro point parameter
    exact (integrable point parameter).const_mul coefficient
  · intro point parameter halfPlane
    have equality : average (fun point => coefficient * continuation parameter point) point =
        coefficient * average (continuation parameter) point := by
      exact integral_const_mul _ _
    exact equality.trans ((congrArg (fun scalar : ℂ => coefficient * scalar)
      (recovery point parameter halfPlane)).trans (congrFun (congrFun sectionEquality parameter) point))

theorem exists_continuation {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation (fun parameter point => sectionFunction (flat.1 parameter) point) continuation := by
  obtain ⟨continuation, continues, _⟩ := exists_recovery flat
  exact ⟨continuation, continues⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryContinuation
