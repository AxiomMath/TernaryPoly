module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.Vectors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Smooth

theorem continuous_of_smooth {matrixSize argumentCount : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : (Fin argumentCount → Matrix.GeneralLinearGroup (Fin matrixSize) ℝ) → Target}
    (smoothFunction : Smooth function) : Continuous function := by
  have continuousValues : Continuous
      (fun matrices : Fin argumentCount → Matrix.GeneralLinearGroup (Fin matrixSize) ℝ =>
        fun index => (matrices index).val) :=
    continuous_pi (fun index => Units.continuous_val.comp (continuous_apply index))
  have continuousComposition := smoothFunction.continuousOn.comp_continuous
    continuousValues (fun matrices index => Matrix.GeneralLinearGroup.det_ne_zero (matrices index))
  have recoverMatrices (matrices : Fin argumentCount →
      Matrix.GeneralLinearGroup (Fin matrixSize) ℝ) :
      (fun index => invertibleMatrix (matrices index).val) = matrices := by
    funext index
    apply Units.ext
    simp [invertibleMatrix, Matrix.GeneralLinearGroup.det_ne_zero]
  change Continuous (fun matrices : Fin argumentCount →
      Matrix.GeneralLinearGroup (Fin matrixSize) ℝ =>
    function (fun index => invertibleMatrix (matrices index).val)) at continuousComposition
  simpa only [recoverMatrices] using continuousComposition

theorem planeCuspVector_continuous {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (basePoint : AdelicGL) :
    Continuous (fun realMatrix : RealGL3 =>
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection
        (basePoint * atInfinity realMatrix)).val) := by
  have continuousLift : Continuous (fun matrices : Fin 1 → RealGL3 =>
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection
        (basePoint * atInfinity (matrices 0))).val) := continuous_of_smooth
    (matrixSize := 3) (argumentCount := 1) (Target := data.cusp.H)
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector_smooth inducedSection basePoint)
  have continuousDiagonal : Continuous
      (fun realMatrix : RealGL3 => fun _ : Fin 1 => realMatrix) :=
    continuous_pi (fun _ => continuous_id)
  convert continuousLift.comp continuousDiagonal using 1
  rfl

theorem planeCuspVector_bound_on_compact {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (basePoint : AdelicGL)
    {compactSet : Set RealGL3} (compactness : IsCompact compactSet) :
    ∃ bound : ℝ, ∀ realMatrix ∈ compactSet,
      ‖(TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector inducedSection
        (basePoint * atInfinity realMatrix)).val‖ ≤ bound :=
  compactness.exists_bound_of_continuousOn
    (planeCuspVector_continuous inducedSection basePoint).continuousOn

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Smooth
