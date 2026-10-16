module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.OrbitTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit

theorem realOrbit_one (data : CuspidalRepresentation) (vector : data.H) :
    realOrbit data vector 1 = vector := by
  unfold realOrbit
  rw [show invertibleMatrix (1 : BinaryMatrix) = 1 from invertibleMatrix_units 1,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, map_one, Module.End.one_apply]

theorem realOrbit_analyticAt_of_one (data : CuspidalRepresentation) (vector : data.H)
    (identityRegularity : AnalyticAt ℝ (realOrbit data vector) 1) (matrix : BinaryRealGL) :
    AnalyticAt ℝ (realOrbit data vector) matrix.val := by
  let inverseTranslation := leftMultiplication matrix⁻¹.val
  let action := (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.unitaryOperator data (atInfinity matrix)).restrictScalars ℝ
  have inverseAtPoint : inverseTranslation matrix.val = (1 : BinaryMatrix) := matrix.inv_val
  have atTranslated : AnalyticAt ℝ (realOrbit data vector) (inverseTranslation matrix.val) :=
    (congrArg (fun point : BinaryMatrix => AnalyticAt ℝ (realOrbit data vector) point)
      inverseAtPoint).mpr identityRegularity
  have composite : AnalyticAt ℝ (action ∘ (realOrbit data vector) ∘ inverseTranslation) matrix.val :=
    (action.analyticAt _).comp (atTranslated.comp (inverseTranslation.analyticAt _))
  have germEquality : realOrbit data vector =ᶠ[nhds matrix.val]
      action ∘ (realOrbit data vector) ∘ inverseTranslation := by
    filter_upwards [binaryDomain_isOpen.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero matrix)]
      with value invertibility
    exact (realOrbit_inverse_translation data vector matrix value invertibility).symm
  exact composite.congr germEquality.symm

theorem realOrbit_analyticOn_of_one (data : CuspidalRepresentation) (vector : data.H)
    (identityRegularity : AnalyticAt ℝ (realOrbit data vector) 1) :
    AnalyticOn ℝ (realOrbit data vector) binaryDomain := by
  intro matrix invertibility
  have regularity := realOrbit_analyticAt_of_one data vector identityRegularity (invertibleMatrix matrix)
  have equality := invertibleMatrix_val matrix invertibility
  have regularityAt : AnalyticAt ℝ (realOrbit data vector) matrix :=
    (congrArg (fun point : BinaryMatrix => AnalyticAt ℝ (realOrbit data vector) point) equality).mp regularity
  exact regularityAt.analyticWithinAt

theorem smooth_realOrbit_of_analyticAt_one (data : CuspidalRepresentation) (vector : data.H)
    (identityRegularity : AnalyticAt ℝ (realOrbit data vector) 1) :
    Smooth (fun matrices : Fin 1 → BinaryRealGL => data.π (atInfinity (matrices 0)) vector) := by
  have orbitRegularity : ContDiffOn ℝ ⊤ (realOrbit data vector) binaryDomain :=
    (realOrbit_analyticOn_of_one data vector identityRegularity).contDiffOn binaryDomain_isOpen.uniqueDiffOn
  have projectionRegularity : ContDiff ℝ ⊤
      (fun matrices : Fin 1 → BinaryMatrix => matrices 0) := by fun_prop
  exact orbitRegularity.comp projectionRegularity.contDiffOn (fun _ membership => membership 0)

theorem fixed_mem_smooth_iff_analyticAt_one (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.H) (fixed : vector ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level) :
    vector ∈ data.smooth ↔ AnalyticAt ℝ (realOrbit data vector) 1 := by
  constructor
  · intro smoothVector
    exact (smooth_orbit_contDiffAt_one data ⟨vector, smoothVector⟩).analyticAt
  · intro analyticVector
    exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.fixed_mem_smooth_iff data level openness compactness vector fixed).mpr
      (smooth_realOrbit_of_analyticAt_one data vector analyticVector)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit
