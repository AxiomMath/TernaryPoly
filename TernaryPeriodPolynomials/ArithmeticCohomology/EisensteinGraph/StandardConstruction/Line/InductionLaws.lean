module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.OrbitLevel

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineInductionLaws

theorem atInfinity_one : atInfinity (1 : RealGL3) = 1 := by
  apply InducedContinuity.adelic_ext
  · simp [InducedContinuity.realGroup_atInfinity]
  · simp [InducedContinuity.finiteGroup_atInfinity]

theorem smoothLift_binaryOrbit_mem {degree arity : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (lift : HasSmoothCuspLift data side parameter function)
    (vertices : Fin arity → RealGL3) (argument : AdelicGL) :
    (fun binary : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det binary)
        (-binaryInductionExponent degree side parameter) *
          function vertices (binaryLevi side binary * argument)) ∈ cuspFunctions data.cusp := by
  obtain ⟨vector, _, realizes⟩ := lift argument
  refine ⟨vector (Fin.snoc vertices (1 : RealGL3)), ?_⟩
  funext binary
  simpa only [Fin.snoc_castSucc, Fin.snoc_last, atInfinity_one, mul_one]
    using realizes (Fin.snoc vertices (1 : RealGL3)) binary

theorem continuation_line_induced_iff {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint) :
    IsInduced data .line cohomologicalPoint (continuation cohomologicalPoint) ↔
      (∀ argument, Smooth (fun real : Fin 1 → RealGL3 =>
        continuation cohomologicalPoint (argument * atInfinity (real 0)))) ∧
      HasSmoothCuspLift data .line cohomologicalPoint
        (fun (_ : Fin 0 → RealGL3) => continuation cohomologicalPoint) := by
  constructor
  · intro induced
    exact ⟨induced.1, induced.2.2.1⟩
  · rintro ⟨smooth, lift⟩
    refine ⟨smooth, ?_, lift, ?_⟩
    · exact StandardInvariance.continuation_finite data extension continuation flat
        continues cohomologicalPoint regular
    · refine ⟨StandardInvariance.continuation_lineRadical extension continuation continues
        cohomologicalPoint regular, ?_, ?_⟩
      · exact StandardRankOne.continuation_rankOne data extension continuation flat
          continues cohomologicalPoint regular
      · intro argument
        simpa only [binaryLevi, binaryInductionExponent] using
          (smoothLift_binaryOrbit_mem data .line cohomologicalPoint
            (fun (_ : Fin 0 → RealGL3) => continuation cohomologicalPoint)
            lift (fun _ => 1) argument)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineInductionLaws
