module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.OrbitIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.LiftCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.HilbertAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicCompactOrbitIntegral

theorem vector_plane_decomposition {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (first second : Adeles)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) (argument : AdelicGL) :
    CuspLift.vector data .plane parameter function induced
      (planeUnipotent first second * planeLevi binary unit * argument) =
      ((data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) *
        normPower (Matrix.GeneralLinearGroup.det binary)
          (binaryInductionExponent degree .plane parameter)) •
        CuspRealization.smoothAction data.cusp binary
          (CuspLift.vector data .plane parameter function induced argument) := by
  rw [mul_assoc, CuspLiftCovariance.vector_plane_radical,
    FlatUniqueness.planeLevi_split, mul_assoc, CuspLiftCovariance.vector_plane_rankOne]
  apply Subtype.ext
  change _ • (CuspLift.vector data .plane parameter function induced
    (binaryLevi .plane binary * argument)).val = _
  rw [CuspLiftCovariance.vector_binary, smul_smul]
  rfl

/-- The compact real orbit integral at an arbitrary adelic base argument is a
smooth vector and realizes the scalar integral at every binary adele. -/
theorem compact_real_orbit_integral {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (argument : AdelicGL)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] (measure : Measure X) [IsFiniteMeasure measure]
    (realMap : X → RealGL3) (realContinuous : Continuous realMap) :
    ∃ vector : data.cusp.smooth,
      vector.val = ∫ point, (CuspLift.vector data .plane parameter function induced
        (argument * atInfinity (realMap point))).val ∂measure ∧
      ∀ test, data.cusp.realize vector test =
        ∫ point, data.cusp.realize (CuspLift.vector data .plane parameter function induced
          (argument * atInfinity (realMap point))) test ∂measure := by
  obtain ⟨first, second, binary, unit, compact, compactMember, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition argument
  obtain ⟨finite, finiteEquality⟩ := compactMember.2
  have compactSplit : compact =
      atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) *
        atInfinity (realGroup compact) := by
    calc
      compact = atInfinity (realGroup compact) * atFinite (finiteGroup compact) :=
        Norm.adelicGL_eq_mul compact
      _ = atInfinity (realGroup compact) *
          atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) := by
        rw [finiteEquality]
      _ = _ := (RealTranslations.atFinite_atInfinity_commute _ _).symm
  let shifted : X → RealGL3 := fun point => realGroup compact * realMap point
  have shiftedContinuous : Continuous shifted := continuous_const.mul realContinuous
  let raw : X → data.cusp.smooth := fun point =>
    CuspLift.vector data .plane parameter function induced
      (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) *
        atInfinity (shifted point))
  let factor : ℂ :=
    (data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) *
      normPower (Matrix.GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter)
  have transformed : ∀ point,
      CuspLift.vector data .plane parameter function induced
        (argument * atInfinity (realMap point)) =
      factor • CuspRealization.smoothAction data.cusp binary (raw point) := by
    intro point
    have argumentEquality : argument * atInfinity (realMap point) =
        planeUnipotent first second * planeLevi binary unit *
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) *
            atInfinity (shifted point)) := by
      rw [decomposition, compactSplit, show shifted point =
        realGroup compact * realMap point from rfl, RealTranslations.atInfinity_mul]
      simp only [mul_assoc]
    rw [argumentEquality]
    exact vector_plane_decomposition data parameter function induced first second binary unit _
  obtain ⟨rawIntegral, hilbert, scalar⟩ := CompactOrbitIntegral.compact_orbit_integral
    data parameter function induced finite measure shifted shiftedContinuous
  let vector : data.cusp.smooth :=
    factor • CuspRealization.smoothAction data.cusp binary rawIntegral
  refine ⟨vector, ?_, ?_⟩
  · let action : data.cusp.H →L[ℂ] data.cusp.H :=
      factor • (CuspHilbertAction.isometry data.cusp binary).toContinuousLinearMap
    have rawContinuous : Continuous (fun point => (raw point).val) :=
      (CuspLift.real_continuous data .plane parameter function induced _).comp shiftedContinuous
    have rawIntegrable : Integrable (fun point => (raw point).val) measure := by
      simpa only [integrableOn_univ] using
        (ContinuousOn.integrableOn_compact (μ := measure) isCompact_univ rawContinuous.continuousOn)
    change action rawIntegral.val = _
    rw [hilbert, ← action.integral_comp_comm rawIntegrable]
    apply integral_congr_ae
    filter_upwards [] with point
    exact (congrArg Subtype.val (transformed point)).symm
  · intro test
    change data.cusp.realize
      (factor • CuspRealization.smoothAction data.cusp binary rawIntegral) test = _
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, CuspRealization.realize_equivariant]
    rw [scalar]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with point
    rw [transformed]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, CuspRealization.realize_equivariant]
    rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicCompactOrbitIntegral
