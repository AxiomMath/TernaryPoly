module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ParameterLattices

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRectangularFourier
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteFourierUniform

theorem transform_bound (compact : Set Space) (compactIs : IsCompact compact)
    (function : Space → ℂ) (supported : ∀ value, value ∉ compact → function value = 0)
    (bound : ℝ) (bounded : ∀ value, ‖function value‖ ≤ bound) (frequency : Space) :
    ‖transform function frequency‖ ≤ bound * measure.real compact := by
  let _ : IsFiniteMeasure (measure.restrict compact) := ⟨by
    simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using compactIs.measure_lt_top (μ := measure)⟩
  have restricted : (∫ value in compact, pairing frequency value * function value ∂measure) = transform function frequency :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun value outside => by rw [supported value outside, mul_zero])
  rw [← restricted]
  have result := norm_integral_le_of_norm_le_const (μ := measure.restrict compact)
    (Filter.Eventually.of_forall (fun value => by
      calc
        ‖pairing frequency value * function value‖ = ‖function value‖ := by rw [norm_mul, pairing_norm, one_mul]
        _ ≤ bound := bounded value))
  simpa only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using result

def test (scale : FiniteAdelesˣ) (offset : Space) (parameter : FiniteParameterThetaDecay.Parameter) : Space → ℂ :=
  fun value => boxTest (fun _ => scale) offset (RectangularAdelicPoisson.finiteTransform parameter.1 parameter.2 value)

theorem test_compactSupport (scale : FiniteAdelesˣ) (offset : Space) (parameter : FiniteParameterThetaDecay.Parameter) :
    HasCompactSupport (test scale offset parameter) :=
  (boxTest_compactSupport (fun _ => scale) offset).comp_homeomorph
    (FiniteLinearLattices.homeomorph (RectangularAdelicPoisson.finiteTransform parameter.1 parameter.2))

theorem test_norm (scale : FiniteAdelesˣ) (offset : Space) (parameter : FiniteParameterThetaDecay.Parameter) (value : Space) :
    ‖test scale offset parameter value‖ ≤ 1 := by
  unfold test
  rw [boxTest_indicator]
  by_cases membership : RectangularAdelicPoisson.finiteTransform parameter.1 parameter.2 value ∈ box (fun _ => scale) offset
  · rw [Set.indicator_of_mem membership]
    norm_num
  · rw [Set.indicator_of_notMem membership]
    norm_num

theorem uniform_support (scale : FiniteAdelesˣ) (offset : Space)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (compact : IsCompact parameters) :
    ∃ hull : Set Space, IsCompact hull ∧ ∀ parameter ∈ parameters,
      ∀ value, value ∉ hull → test scale offset parameter value = 0 := by
  let baseTest := (boxTest (fun _ => scale) offset) ∘ AdelicThetaDecay.coordinateHomeomorph
  have baseSupport : HasCompactSupport baseTest :=
    (boxTest_compactSupport (fun _ => scale) offset).comp_homeomorph AdelicThetaDecay.coordinateHomeomorph
  obtain ⟨hull, hullCompact, supported⟩ := FiniteParameterThetaDecay.exists_hull baseTest baseSupport parameters compact
  refine ⟨AdelicThetaDecay.coordinateHomeomorph '' hull, hullCompact.image AdelicThetaDecay.coordinateHomeomorph.continuous, ?_⟩
  intro parameter membership value outside
  have matrixOutside : AdelicThetaDecay.coordinateHomeomorph.symm value ∉ hull := by
    intro inside
    exact outside ⟨_, inside, AdelicThetaDecay.coordinateHomeomorph.apply_symm_apply value⟩
  exact supported parameter membership _ matrixOutside

theorem uniform_transform (scale : FiniteAdelesˣ) (offset : Space)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (compact : IsCompact parameters) :
    ∃ (hull : Set Space) (bound : ℝ), IsCompact hull ∧ 0 ≤ bound ∧ ∀ parameter ∈ parameters,
      (∀ frequency, frequency ∉ hull → transform (test scale offset parameter) frequency = 0) ∧
      (∀ frequency, ‖transform (test scale offset parameter) frequency‖ ≤ bound) := by
  obtain ⟨rational, invariant⟩ := FiniteParameterLattices.box_uniform_periodic scale offset parameters compact
  obtain ⟨supportHull, supportCompact, supported⟩ := uniform_support scale offset parameters compact
  refine ⟨(FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale rational)⁻¹ : Set Space),
    measure.real supportHull, FiniteSchwartzClosure.latticeSubgroup_compact _, ENNReal.toReal_nonneg, ?_⟩
  intro parameter membership
  refine ⟨fun frequency outside => FiniteSchwartzClosure.transform_outside _ _ (test_compactSupport scale offset parameter)
    (invariant parameter membership) frequency outside, fun frequency => ?_⟩
  simpa only [one_mul] using transform_bound supportHull supportCompact (test scale offset parameter)
    (supported parameter membership) 1 (test_norm scale offset parameter) frequency

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteFourierUniform
