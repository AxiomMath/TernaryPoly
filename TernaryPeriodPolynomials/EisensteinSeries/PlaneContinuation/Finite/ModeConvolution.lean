module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.HilbertConvolution

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteModeConvolution

def translated (data : CuspidalRepresentation) (vector : data.smooth) (binary : BinaryFiniteGL) : data.smooth :=
  ⟨data.π (atFinite binary) vector.val, data.smooth_stable _ _ vector.property⟩

theorem averaged_mode {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (binary : BinaryFiniteGL) :
    smoothAverage data.cusp finiteCongruence finiteCongruence_isCompact (translated data.cusp vector.val binary) ∈
      fixedMode data.cusp finiteCongruence index := by
  apply (mem_fixedMode_iff data.cusp finiteCongruence index _).mpr
  refine ⟨averagingOperator_mem_fixedSubspace data.cusp finiteCongruence _, ?_⟩
  intro parameter
  change data.cusp.π (atInfinity (RotationCircle.rotation parameter))
    (averagingOperator data.cusp finiteCongruence (data.cusp.π (atFinite binary) vector.val.val)) = _
  rw [← averagingOperator_real]
  have commute : data.cusp.π (atInfinity (RotationCircle.rotation parameter))
      (data.cusp.π (atFinite binary) vector.val.val) =
        data.cusp.π (atFinite binary) (data.cusp.π (atInfinity (RotationCircle.rotation parameter)) vector.val.val) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      FiniteLevel.atFinite_atInfinity_commute]
  rw [commute, ((mem_fixedMode_iff data.cusp finiteCongruence index vector.val).mp vector.property).2 parameter,
    map_smul, map_smul]
  rfl

def orbit {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (binary : BinaryFiniteGL) :
    fixedMode data.cusp finiteCongruence index :=
  ⟨smoothAverage data.cusp finiteCongruence finiteCongruence_isCompact (translated data.cusp vector.val binary),
    averaged_mode data index vector binary⟩

theorem orbit_hilbert {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (binary : BinaryFiniteGL) :
    (orbit data index vector binary).val.val =
      averagingOperator data.cusp finiteCongruence (data.cusp.π (atFinite binary) vector.val.val) := rfl

theorem orbit_continuous {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) : Continuous (orbit data index vector) :=
  (((averagingOperator data.cusp finiteCongruence).continuous.comp
    ((data.cusp.continuous vector.val.val).comp atFinite_continuous)).subtype_mk _).subtype_mk _

theorem orbit_norm {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (binary : BinaryFiniteGL) :
    ‖orbit data index vector binary‖ ≤ ‖vector‖ := by
  change ‖averagingOperator data.cusp finiteCongruence (data.cusp.π (atFinite binary) vector.val.val)‖ ≤ ‖vector.val.val‖
  calc
    _ ≤ ‖averagingOperator data.cusp finiteCongruence‖ * ‖data.cusp.π (atFinite binary) vector.val.val‖ :=
      (averagingOperator data.cusp finiteCongruence).le_opNorm _
    _ ≤ ‖data.cusp.π (atFinite binary) vector.val.val‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (averagingOperator_norm_le data.cusp finiteCongruence)
    _ = _ := data.cusp.unitary _ _

theorem orbit_integrable {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) :
    Integrable (fun binary => coefficient binary • orbit data index vector binary) BinaryProductHaar.finiteMeasure := by
  apply (integrable.norm.mul_const ‖vector‖).mono'
    (integrable.aestronglyMeasurable.smul (orbit_continuous data index vector).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro binary
  change ‖coefficient binary • orbit data index vector binary‖ ≤ ‖coefficient binary‖ * ‖vector‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (orbit_norm data index vector binary) (norm_nonneg _)

def inclusion {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    fixedMode data.cusp finiteCongruence index →L[ℂ] data.cusp.H :=
  data.cusp.smooth.subtypeL.comp (fixedMode data.cusp finiteCongruence index).subtypeL

theorem modeMap_integral {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) :
    modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact coefficient integrable index vector =
      ∫ binary, coefficient binary • orbit data index vector binary ∂BinaryProductHaar.finiteMeasure := by
  let _ := EndpointAdmissibility.all_finiteDimensional data index
  apply Subtype.ext
  apply Subtype.ext
  change averagingOperator data.cusp finiteCongruence
      (∫ binary, coefficient binary • data.cusp.π (atFinite binary) vector.val.val ∂BinaryProductHaar.finiteMeasure) =
    inclusion data index (∫ binary, coefficient binary • orbit data index vector binary ∂BinaryProductHaar.finiteMeasure)
  rw [← (averagingOperator data.cusp finiteCongruence).integral_comp_comm
      (integrand_integrable data.cusp coefficient integrable vector.val.val),
    ← (inclusion data index).integral_comp_comm (orbit_integrable data index vector coefficient integrable)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro binary
  dsimp only
  rw [map_smul, map_smul]
  rfl

def evaluation {degree : ℕ} (data : InducingData degree) (index : ℤ) (point : BinaryAdelicGL) :
    fixedMode data.cusp finiteCongruence index →L[ℂ] ℂ := by
  let _ := EndpointAdmissibility.all_finiteDimensional data index
  let linear : fixedMode data.cusp finiteCongruence index →ₗ[ℂ] ℂ :=
    ((LinearMap.proj point).comp data.cusp.realize).comp (fixedMode data.cusp finiteCongruence index).subtype
  exact ⟨linear, linear.continuous_of_finiteDimensional⟩

theorem realize_modeMap {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) (point : BinaryAdelicGL) :
    data.cusp.realize (modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
      coefficient integrable index vector).val point =
      ∫ binary, coefficient binary * data.cusp.realize (orbit data index vector binary).val point
        ∂BinaryProductHaar.finiteMeasure := by
  let _ := EndpointAdmissibility.all_finiteDimensional data index
  change evaluation data index point (modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
    coefficient integrable index vector) = _
  rw [modeMap_integral, ← (evaluation data index point).integral_comp_comm
    (orbit_integrable data index vector coefficient integrable)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun binary => by dsimp only; rw [map_smul]; rfl)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteModeConvolution
