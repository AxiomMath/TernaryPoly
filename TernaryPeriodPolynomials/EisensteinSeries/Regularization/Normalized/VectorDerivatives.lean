module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.VectorParameters
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.NormalizationSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.SmoothSeminorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedCuspVector_realOrbit_smooth
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) :
    Smooth (fun realElements : Fin 1 → RealGL3 =>
      (normalizedCuspVector induced parameter (matrix * atInfinity (realElements 0))).val) :=
  (smooth_normPower_det matrix (-((degree : ℂ) + 3) / 3)).smul
    (inducedCuspVector_realOrbit_smooth (induced (parameter - ((degree : ℂ) + 3) / 2)) matrix)

theorem normalizedCuspVector_realOrbit_derivative_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (order : ℕ) :
    Continuous (fun realElements : Fin 1 → RealGL3 =>
      iteratedFDeriv ℝ order
        (fun entries : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
          (normalizedCuspVector induced parameter
            (matrix * atInfinity (invertibleMatrix (entries 0)))).val)
        (fun index => (realElements index).val)) :=
  smooth_iteratedFDeriv_continuous (normalizedCuspVector_realOrbit_smooth induced parameter matrix) order

theorem normalizedCuspVector_realOrbit_derivative_compact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) (order : ℕ)
    {domain : Set (Fin 1 → RealGL3)} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realElements ∈ domain,
      ‖iteratedFDeriv ℝ order
        (fun entries : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
          (normalizedCuspVector induced parameter
            (matrix * atInfinity (invertibleMatrix (entries 0)))).val)
        (fun index => (realElements index).val)‖ ≤ bound :=
  smooth_iteratedFDeriv_compact_bound
    (normalizedCuspVector_realOrbit_smooth induced parameter matrix) order compact

theorem normalizedCuspVector_cuspDerivative_exponential
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    ∃ weight : ℝ, ∀ order : ℕ, ∀ parameter : ℂ,
      cuspOrbitDerivative inducingData.cusp order (normalizedCuspVector flat.1 parameter matrix) =
        Complex.exp (parameter * (weight : ℂ)) •
          cuspOrbitDerivative inducingData.cusp order (normalizedCuspVector flat.1 0 matrix) := by
  obtain ⟨weight, scaling⟩ := normalizedCuspVector_exponential flat matrix
  exact ⟨weight, fun order parameter => by rw [scaling parameter, map_smul]⟩

theorem normalizedCuspVector_cuspDerivative_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (order : ℕ) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby =>
      cuspOrbitDerivative inducingData.cusp order (normalizedCuspVector flat.1 nearby matrix)) parameter := by
  obtain ⟨weight, scaling⟩ := normalizedCuspVector_cuspDerivative_exponential flat matrix
  have equality : (fun nearby =>
      cuspOrbitDerivative inducingData.cusp order (normalizedCuspVector flat.1 nearby matrix)) =
      (fun nearby => Complex.exp (nearby * (weight : ℂ)) •
        cuspOrbitDerivative inducingData.cusp order (normalizedCuspVector flat.1 0 matrix)) :=
    funext (scaling order)
  rw [equality]
  exact ((analyticAt_id.mul analyticAt_const).cexp).smul analyticAt_const

theorem normalizedCuspVector_cuspSeminorm_compact_parameter_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (order : ℕ)
    {parameters : Set ℂ} (compact : IsCompact parameters) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameters,
      cuspSmoothSeminorm inducingData.cusp order (normalizedCuspVector flat.1 parameter matrix) ≤ bound := by
  have continuous : Continuous (fun parameter =>
      cuspOrbitDerivative inducingData.cusp order (normalizedCuspVector flat.1 parameter matrix)) :=
    continuous_iff_continuousAt.mpr (fun parameter =>
      (normalizedCuspVector_cuspDerivative_analytic flat matrix order parameter).continuousAt)
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuous.continuousOn
  exact ⟨max 0 bound, le_max_left _ _, fun parameter member =>
    (bounded parameter member).trans (le_max_right _ _)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
