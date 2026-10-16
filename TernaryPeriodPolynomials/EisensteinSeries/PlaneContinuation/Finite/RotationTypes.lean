module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Banach
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Scalar

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open scoped NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes

noncomputable def fixedMode (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (index : ℤ) :
    Submodule ℂ data.smooth := fixedSmooth data level ⊓ LinearMap.ker (smoothMode data index - LinearMap.id)

theorem mem_fixedMode_iff (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (index : ℤ) (vector : data.smooth) : vector ∈ fixedMode data level index ↔
      vector.val ∈ fixedSubspace data level ∧ ∀ parameter : TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle.Parameter,
        data.π (atInfinity (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle.rotation parameter)) vector.val =
          fourier index parameter • vector.val := by
  constructor
  · intro membership
    refine ⟨membership.1, ?_⟩
    have equality : smoothMode data index vector = vector := sub_eq_zero.mp membership.2
    have vectorEquality : modeVector data index vector.val = vector.val := congrArg Subtype.val equality
    intro parameter
    have eigen := modeVector_eigen data index vector.val parameter
    rw [vectorEquality] at eigen
    exact eigen
  · rintro ⟨fixed, eigen⟩
    refine ⟨fixed, ?_⟩
    change smoothMode data index vector - vector = 0
    exact sub_eq_zero.mpr (Subtype.ext (modeVector_eq_self_of_eigen data index vector.val eigen))

theorem smoothMode_mem_fixedMode (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (index : ℤ) (vector : fixedSmooth data level) : smoothMode data index vector.val ∈ fixedMode data level index := by
  constructor
  · exact (modeVector_preserves_fixedSmooth data index level openness compactness vector.val vector.property).2
  · change smoothMode data index (smoothMode data index vector.val) - smoothMode data index vector.val = 0
    apply sub_eq_zero.mpr
    exact Subtype.ext (modeVector_idempotent data index vector.val.val)

noncomputable def fixedModeProjection (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (index : ℤ) : fixedSmooth data level →ₗ[ℂ] fixedMode data level index :=
  ((smoothMode data index).comp (fixedSmooth data level).subtype).codRestrict
    (fixedMode data level index) (smoothMode_mem_fixedMode data level openness compactness index)

theorem fixedModeProjection_continuous {Source : Type*} [TopologicalSpace Source]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (index : ℤ) (family : Source → fixedSmooth data level)
    (hilbertContinuous : Continuous (fun parameter => (family parameter).val.val)) :
    Continuous (fun parameter => fixedModeProjection data level openness compactness index (family parameter)) := by
  have continuity := (modeOperator data index).continuous.comp hilbertContinuous
  exact (continuity.subtype_mk _).subtype_mk _

theorem scalar_mode_continuous {Source : Type*} [TopologicalSpace Source]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (index : ℤ) [FiniteDimensional ℂ (fixedMode data level index)]
    (family : Source → fixedSmooth data level)
    (hilbertContinuous : Continuous (fun parameter => (family parameter).val.val)) (point : BinaryAdelicGL) :
    Continuous (fun parameter => data.realize (smoothMode data index (family parameter).val) point) := by
  let evaluation : fixedMode data level index →ₗ[ℂ] ℂ :=
    (LinearMap.proj point).comp (data.realize.comp (fixedMode data level index).subtype)
  exact evaluation.continuous_of_finiteDimensional.comp
    (fixedModeProjection_continuous data level openness compactness index family hilbertContinuous)

/-- Admissibility at a finite level gives continuity for every Banach-parameterized analytic family. -/
theorem realization_continuous_of_finite_types {Source : Type*} [NormedAddCommGroup Source]
    [NormedSpace ℂ Source] [CompleteSpace Source]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (finiteTypes : ∀ index : ℤ, FiniteDimensional ℂ (fixedMode data level index))
    (family : Source →ₗ[ℂ] fixedSmooth data level)
    (hilbertContinuous : Continuous (fun parameter => (family parameter).val.val)) :
    Continuous (fun parameter => boundedRealization data (family parameter).val) := by
  let lifted : Source →ₗ[ℂ] RotationBanach.orbitSpace :=
    (RotationBanach.realization data).comp ((fixedSmooth data level).subtype.comp family)
  have liftContinuous : Continuous lifted := by
    apply RotationBanach.continuous_of_coefficients
    intro point index
    let _ : FiniteDimensional ℂ (fixedMode data level index) := finiteTypes index
    have scalarContinuous := scalar_mode_continuous data level openness compactness index family hilbertContinuous point
    have equality : (fun parameter : Source => RotationBanach.coefficient point index (lifted parameter)) =
        (fun parameter : Source => data.realize (smoothMode data index (family parameter).val) point) := by
      funext parameter
      exact RotationBanach.coefficient_realization data point index (family parameter).val
    rw [equality]
    exact scalarContinuous
  exact RotationBanach.orbitSpace.subtypeL.continuous.comp liftContinuous

theorem stageRealization_continuous_of_finite_types (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (finiteTypes : ∀ index : ℤ, FiniteDimensional ℂ (fixedMode data level index))
    (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    Continuous (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticRealization.stageRealization data level openness compactness radius positiveRadius) :=
  realization_continuous_of_finite_types data level openness compactness finiteTypes
    (stageSmoothMap data level openness compactness radius positiveRadius)
    (stageHilbertMap data level radius positiveRadius).continuous

theorem continuousStages_of_finite_types (data : CuspidalRepresentation)
    (finiteTypes : ∀ index : ℤ, FiniteDimensional ℂ (fixedMode data finiteCongruence index)) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar.ContinuousStages data :=
  stageRealization_continuous_of_finite_types data finiteCongruence
    finiteCongruence_isOpen finiteCongruence_isCompact finiteTypes

theorem hasSum_of_finite_types {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (finiteTypes : ∀ index : ℤ, FiniteDimensional ℂ (fixedMode data.cusp finiteCongruence index))
    (basePoint : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) :=
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar.hasSum_of_stage_continuity flatSection
    (continuousStages_of_finite_types data.cusp finiteTypes) basePoint parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes
