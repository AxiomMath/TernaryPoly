module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ScalarBinaryContinuation

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarBinaryCenter

theorem cuspIntegrand_center {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (unit : Adelesˣ) (binary : BinaryAdelicGL)
    (argument : AdelicGL) (coordinates : Adeles × Adeles) :
    ScalarBinaryIntegral.cuspIntegrand data parameter function induced
        (GeneralLinearGroup.scalar (Fin 2) unit * binary) argument coordinates =
      data.cusp.centralCharacter unit *
        ScalarBinaryIntegral.cuspIntegrand data parameter function induced
          binary argument coordinates :=
  data.cusp.central unit
    (CuspLift.vector data .plane parameter function induced
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)) binary

theorem normalized_center {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (unit : Adelesˣ) (binary : BinaryAdelicGL) (argument : AdelicGL) :
    ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        (GeneralLinearGroup.scalar (Fin 2) unit * binary) argument cohomologicalPoint =
      data.cusp.centralCharacter unit *
        ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
          binary argument cohomologicalPoint := by
  obtain ⟨threshold, integrals⟩ :=
    ScalarBinaryContinuation.normalized_halfPlane data extension continuation flat continues
  apply ContinuationUniqueness.meromorphic_halfPlane_unique
    (ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
      (GeneralLinearGroup.scalar (Fin 2) unit * binary) argument)
    (fun parameter => data.cusp.centralCharacter unit *
      ScalarBinaryContinuation.normalizedCuspContinuation degree continuation
        binary argument parameter)
    (fun parameter => ScalarBinaryContinuation.normalized_meromorphic extension continuation
      continues _ _ parameter)
    (fun parameter => analyticAt_const.meromorphicAt.mul
      (ScalarBinaryContinuation.normalized_meromorphic extension continuation
        continues _ _ parameter))
    threshold _ cohomologicalPoint
    (ScalarBinaryContinuation.normalized_regular continuation regular _ argument)
    (analyticAt_const.mul
      (ScalarBinaryContinuation.normalized_regular continuation regular binary argument))
  intro parameter large
  rw [integrals parameter large (GeneralLinearGroup.scalar (Fin 2) unit * binary) argument,
    integrals parameter large binary argument]
  simp_rw [cuspIntegrand_center data parameter (extension parameter) (flat.1 parameter)
    unit binary argument]
  exact integral_const_mul _ _

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarBinaryCenter
