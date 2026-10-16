module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.IntervalIntegral

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem analyticAt_intervalIntegral_endpoint {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (function : P × ℝ → F) (point : P) (endpoint : ℝ)
    (continuous : ∀ parameter, Continuous (fun sample => function (parameter, sample)))
    (analytic : ∀ sample, AnalyticAt ℝ function (point, sample)) :
    AnalyticAt ℝ (fun parameter : P × ℝ => ∫ sample in 0..parameter.2, function (parameter.1, sample))
      (point, endpoint) := by
  let integrand (parameter : (P × ℝ) × ℝ) := parameter.1.2 • function (parameter.1.1, parameter.1.2 * parameter.2)
  have integrand_continuous (parameter : P × ℝ) : Continuous (fun sample => integrand (parameter, sample)) := by
    change Continuous (fun sample => parameter.2 • function (parameter.1, parameter.2 * sample))
    exact continuous_const.smul ((continuous parameter.1).comp (continuous_const.mul continuous_id))
  have integrand_analytic (sample : ℝ) : AnalyticAt ℝ integrand ((point, endpoint), sample) := by
    have inner : AnalyticAt ℝ (fun parameter : (P × ℝ) × ℝ =>
        (parameter.1.1, parameter.1.2 * parameter.2)) ((point, endpoint), sample) :=
      (analyticAt_fst.comp analyticAt_fst).prod ((analyticAt_snd.comp analyticAt_fst).mul analyticAt_snd)
    exact (analyticAt_snd.comp analyticAt_fst).smul ((analytic (endpoint * sample)).comp
      (f := fun parameter : (P × ℝ) × ℝ => (parameter.1.1, parameter.1.2 * parameter.2)) inner)
  have integrated := analyticAt_intervalIntegral integrand (point, endpoint) Set.univ isOpen_univ (Set.mem_univ _)
    (fun parameter _ => integrand_continuous parameter) integrand_analytic 0 1
  convert integrated using 1
  funext parameter
  dsimp only [integrand]
  rw [intervalIntegral.integral_smul]
  simpa only [mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (fun sample => function (parameter.1, sample)) parameter.2
      (a := 0) (b := 1)).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
