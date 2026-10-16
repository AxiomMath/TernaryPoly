module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Circle
public import Mathlib.Analysis.Normed.Module.Dual

@[expose] public section


open MeasureTheory TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierUniqueness

theorem scalar_eq_zero (function : C(Parameter, ℂ))
    (coefficients : ∀ index : ℤ, fourierCoeff function index = 0) : function = 0 := by
  have zeroCoefficients : fourierCoeff function = 0 := funext coefficients
  have summability : Summable (fourierCoeff function) := by
    rw [zeroCoefficients]
    exact summable_zero
  have expansion := hasSum_fourier_series_of_summable summability
  have zeroSummand : (fun index : ℤ => fourierCoeff function index • fourier index) =
      (fun _ : ℤ => (0 : C(Parameter, ℂ))) := by
    funext index
    rw [coefficients index]
    exact zero_smul ℂ (fourier index)
  rw [zeroSummand] at expansion
  exact expansion.unique hasSum_zero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem map_fourierCoeff (function : Parameter → E) (continuity : Continuous function)
    (map : E →L[ℂ] F) (index : ℤ) :
    fourierCoeff (fun point => map (function point)) index = map (fourierCoeff function index) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  have integrability : Integrable (fun point => fourier (-index) point • function point)
      AddCircle.haarAddCircle :=
    ((fourier (-index)).continuous.smul continuity).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold fourierCoeff
  calc
    _ = ∫ point : Parameter, map (fourier (-index) point • function point) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => (map.map_smul _ _).symm)
    _ = _ := map.integral_comp_comm integrability

theorem eq_zero (function : Parameter → E) (continuity : Continuous function)
    (coefficients : ∀ index : ℤ, fourierCoeff function index = 0) : function = 0 := by
  funext point
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro functional
  have scalarCoefficients (index : ℤ) :
      fourierCoeff (fun point => functional (function point)) index = 0 := by
    rw [map_fourierCoeff function continuity functional, coefficients, map_zero]
  have scalarEquality := scalar_eq_zero
    ⟨fun point => functional (function point), functional.continuous.comp continuity⟩ scalarCoefficients
  exact congrArg (fun continuousFunction : C(Parameter, ℂ) => continuousFunction point) scalarEquality

theorem fourierCoeff_smul_vector (function : Parameter → ℂ) (continuity : Continuous function)
    (vector : E) (index : ℤ) :
    fourierCoeff (fun point => function point • vector) index = fourierCoeff function index • vector :=
  map_fourierCoeff function continuity (ContinuousLinearMap.toSpanSingleton ℂ vector) index

omit [CompleteSpace E] in
theorem fourierCoeff_sub (first second : Parameter → E)
    (continuousFirst : Continuous first) (continuousSecond : Continuous second) (index : ℤ) :
    fourierCoeff (fun point => first point - second point) index =
      fourierCoeff first index - fourierCoeff second index := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  unfold fourierCoeff
  have firstIntegrability : Integrable (fun point => fourier (-index) point • first point)
      AddCircle.haarAddCircle :=
    ((fourier (-index)).continuous.smul continuousFirst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have secondIntegrability : Integrable (fun point => fourier (-index) point • second point)
      AddCircle.haarAddCircle :=
    ((fourier (-index)).continuous.smul continuousSecond).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [smul_sub]
  exact integral_sub firstIntegrability secondIntegrability

theorem ext (first second : Parameter → E)
    (continuousFirst : Continuous first) (continuousSecond : Continuous second)
    (coefficients : ∀ index : ℤ, fourierCoeff first index = fourierCoeff second index) : first = second := by
  have differenceZero : (fun point => first point - second point) = 0 :=
    eq_zero _ (continuousFirst.sub continuousSecond) (fun index => by
      rw [fourierCoeff_sub first second continuousFirst continuousSecond, coefficients, sub_self])
  funext point
  exact sub_eq_zero.mp (congrFun differenceZero point)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierUniqueness
