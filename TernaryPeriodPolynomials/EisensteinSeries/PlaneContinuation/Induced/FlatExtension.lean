module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.ParameterShift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ParameterShiftHeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedParameterShift

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedFlatExtension

theorem coefficient_of_compact (difference : ℂ) (point : AdelicGL) (compact : inMaximalCompact point) :
    coefficient difference point = 1 := by
  have heightZero : GlobalHeight.height point = 0 :=
    (HeightProperties.height_of_factorization point 1 point (by simp) compact).trans HeightProperties.planeHeightLog_one
  rw [coefficient, heightZero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem parameter_analytic (source : ℂ) (value : AdelicGL → ℂ) (point : AdelicGL) (parameter : ℂ) :
    AnalyticAt ℂ (fun target => function source target value point) parameter := by
  exact (((analyticAt_id.sub analyticAt_const).mul analyticAt_const).cexp').mul analyticAt_const

theorem flat {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (original : IsInduced data .plane source value) : IsFlatSection data (fun target => function source target value) := by
  refine ⟨induced original, parameter_analytic source value, ?_⟩
  intro target binary point compact
  change normPower (Matrix.GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane target) *
    function source target value (planeLevi binary 1 * point) =
      normPower (Matrix.GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane cohomologicalPoint) *
        function source cohomologicalPoint value (planeLevi binary 1 * point)
  rw [function, function, ← mul_assoc, cusp_factor degree source target point binary,
    ← mul_assoc, cusp_factor degree source cohomologicalPoint point binary,
    coefficient_of_compact _ point compact, coefficient_of_compact _ point compact]

theorem self (source : ℂ) (value : AdelicGL → ℂ) : function source source value = value := by
  funext point
  simp only [function, coefficient, sub_self, zero_mul, Complex.exp_zero, one_mul]

theorem exists_flat {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (original : IsInduced data .plane source value) :
    ∃ family : ℂ → AdelicGL → ℂ, IsFlatSection data family ∧ family source = value :=
  ⟨fun target => function source target value, flat original, self source value⟩

theorem flat_eq_extension {degree : ℕ} {data : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data family) (source target : ℂ) :
    family target = function source target (family source) := by
  funext point
  exact GlobalHeight.flatSection_change_parameter flat point target source

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedFlatExtension
