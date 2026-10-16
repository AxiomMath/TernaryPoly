module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Siegel.ShellMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShells TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShellMeasure

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ShellIntegration

theorem integrableOn_union {Space : Type*} [MeasurableSpace Space]
    {Index : Type*} [Countable Index] (measure : Measure Space)
    (sets : Index → Set Space) (setsMeasurable : ∀ index, MeasurableSet (sets index))
    (volume : ENNReal) (volumeFinite : volume < ⊤)
    (volumeBound : ∀ index, measure (sets index) ≤ volume)
    (function : Space → ℂ) (measurable : Measurable function)
    (bounds : Index → ℝ) (nonnegative : ∀ index, 0 ≤ bounds index)
    (summable : Summable bounds)
    (bounded : ∀ index, ∀ point ∈ sets index, ‖function point‖ ≤ bounds index) :
    IntegrableOn function (⋃ index, sets index) measure := by
  have constantIntegrable (index : Index) : IntegrableOn (fun _ : Space => bounds index) (sets index) measure :=
    integrableOn_const (lt_of_le_of_lt (volumeBound index) volumeFinite).ne
  have integrable (index : Index) : IntegrableOn function (sets index) measure :=
    (constantIntegrable index).mono' measurable.aestronglyMeasurable
      ((ae_restrict_mem (setsMeasurable index)).mono (fun point membership => bounded index point membership))
  apply integrableOn_iUnion_of_summable_integral_norm integrable
  apply Summable.of_nonneg_of_le (fun index => integral_nonneg (fun point => norm_nonneg _))
    (fun index => ?_) (summable.mul_left volume.toReal)
  calc
    _ ≤ ∫ _ in sets index, bounds index ∂measure :=
      setIntegral_mono_on (integrable index).norm (constantIntegrable index) (setsMeasurable index) (bounded index)
    _ = (measure (sets index)).toReal * bounds index := by simp only [integral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, Measure.real]
    _ ≤ volume.toReal * bounds index := mul_le_mul_of_nonneg_right
      (ENNReal.toReal_mono volumeFinite.ne (volumeBound index)) (nonnegative index)

theorem integrable_region (function : BinaryAdelicGL → ℂ) (measurable : Measurable function)
    (bounds : ℤ × ℕ → ℝ) (nonnegative : ∀ index, 0 ≤ bounds index) (summable : Summable bounds)
    (bounded : ∀ (integer : ℤ) (natural : ℕ) (parameter : Parameter),
      ‖function (parameterize integer natural parameter)‖ ≤ bounds (integer, natural)) :
    IntegrableOn function AdelicSiegelCover.region BinaryHaar.measure := by
  have result := integrableOn_union BinaryHaar.measure (fun index : ℤ × ℕ => shell index.1 index.2)
    (fun index => (shell_compact index.1 index.2).measurableSet)
    (BinaryHaar.measure (shell 0 0)) core_finite (fun index => measure_shell_le index.1 index.2)
    function measurable bounds nonnegative summable (by
      rintro ⟨integer, natural⟩ point ⟨parameter, rfl⟩
      exact bounded integer natural parameter)
  simpa only [Set.iUnion_prod', ← region_eq_union] using result

theorem integrable_domain (function : BinaryAdelicGL → ℂ) (measurable : Measurable function)
    (invariant : ∀ rational : BinaryRationalGL, ∀ point,
      function (Matrix.GeneralLinearGroup.map rationalAdele rational * point) = function point)
    (bounds : ℤ × ℕ → ℝ) (nonnegative : ∀ index, 0 ≤ bounds index) (summable : Summable bounds)
    (bounded : ∀ (integer : ℤ) (natural : ℕ) (parameter : Parameter),
      ‖function (parameterize integer natural parameter)‖ ≤ bounds (integer, natural)) :
    IntegrableOn function BinaryFundamentalDomain.domain BinaryHaar.measure :=
  SiegelIntegration.integrableOn function measurable invariant
    (integrable_region function measurable bounds nonnegative summable bounded)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ShellIntegration
