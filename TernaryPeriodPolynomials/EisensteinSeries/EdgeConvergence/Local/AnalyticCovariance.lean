module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Analytic

@[expose] public section


/-!
# Covariance of the local Hilbert standard integral

The local standard integral is linear in the plane section, invariant under finite level
translations of the argument, equivariant under right translations by the real group, and
invariant under left translations by the local line radical `(ℝ × ℚ₃)²`. The proofs are those of
`HilbertStandard.value_finite_invariant`, `HilbertStandard.value_radical_invariant` and
`HilbertStandardAlgebra.value_right_real` for the global integral.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

theorem localValue_finite_invariant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (level : finiteLevel) (argument : AdelicGL) :
    localValue data parameter function induced (argument * atFinite level.val) =
      localValue data parameter function induced argument := by
  unfold localValue localIntegrand
  apply integral_congr_ae
  filter_upwards [] with coordinates
  rw [← mul_assoc, CuspLift.finite_invariant]

theorem localIntegrand_rightReal {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (sectionValue : SectionSpace.inducedSections data .plane parameter) (real : RealGL3)
    (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter
        (RealTranslations.sectionRightReal data .plane parameter real sectionValue).val
        (RealTranslations.sectionRightReal data .plane parameter real sectionValue).property
        argument coordinates =
      localIntegrand data parameter sectionValue.val sectionValue.property
        (argument * atInfinity real) coordinates := by
  have equality := congrArg Subtype.val (HilbertStandardAlgebra.lift_right_real data .plane
    parameter sectionValue real (weyl⁻¹ * localRadical coordinates * argument))
  simpa only [HilbertStandardAlgebra.liftLinear, LinearMap.coe_mk, AddHom.coe_mk, localIntegrand,
    mul_assoc] using equality

/-- Right translation of the plane section by a real element is right translation of the
argument. -/
theorem localValue_rightReal {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (sectionValue : SectionSpace.inducedSections data .plane parameter) (real : RealGL3)
    (argument : AdelicGL) :
    localValue data parameter
        (RealTranslations.sectionRightReal data .plane parameter real sectionValue).val
        (RealTranslations.sectionRightReal data .plane parameter real sectionValue).property
        argument =
      localValue data parameter sectionValue.val sectionValue.property
        (argument * atInfinity real) := by
  unfold localValue
  apply integral_congr_ae
  filter_upwards [] with coordinates
  exact localIntegrand_rightReal data parameter sectionValue real argument coordinates

theorem localIntegrand_add {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (first second : SectionSpace.inducedSections data .plane parameter)
    (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter (first + second).val (first + second).property argument
        coordinates =
      localIntegrand data parameter first.val first.property argument coordinates +
        localIntegrand data parameter second.val second.property argument coordinates :=
  congrArg Subtype.val ((HilbertStandardAlgebra.liftLinear data .plane parameter
    (weyl⁻¹ * localRadical coordinates * argument)).map_add first second)

theorem localIntegrand_smul {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (scalar : ℂ) (sectionValue : SectionSpace.inducedSections data .plane parameter)
    (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter (scalar • sectionValue).val (scalar • sectionValue).property
        argument coordinates =
      scalar • localIntegrand data parameter sectionValue.val sectionValue.property argument
        coordinates :=
  congrArg Subtype.val ((HilbertStandardAlgebra.liftLinear data .plane parameter
    (weyl⁻¹ * localRadical coordinates * argument)).map_smul scalar sectionValue)

/-- Additivity of the local standard integral in the section, for sections with integrable
integrands. -/
theorem localValue_add {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (first second : SectionSpace.inducedSections data .plane parameter) (argument : AdelicGL)
    (firstIntegrable : Integrable
      (localIntegrand data parameter first.val first.property argument) localRadicalMeasure)
    (secondIntegrable : Integrable
      (localIntegrand data parameter second.val second.property argument) localRadicalMeasure) :
    localValue data parameter (first + second).val (first + second).property argument =
      localValue data parameter first.val first.property argument +
        localValue data parameter second.val second.property argument := by
  unfold localValue
  simp_rw [localIntegrand_add]
  exact integral_add firstIntegrable secondIntegrable

theorem localValue_smul {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (scalar : ℂ) (sectionValue : SectionSpace.inducedSections data .plane parameter)
    (argument : AdelicGL) :
    localValue data parameter (scalar • sectionValue).val (scalar • sectionValue).property
        argument =
      scalar • localValue data parameter sectionValue.val sectionValue.property argument := by
  unfold localValue
  simp_rw [localIntegrand_smul]
  exact integral_smul scalar _

theorem localAdele_add (first second : LocalLine) :
    localAdele (first + second) = localAdele first + localAdele second :=
  Prod.ext rfl (finiteAtThreeAdd.map_add first.2 second.2)

local instance normalizedLocalThreeMeasure_isAddHaar' :
    normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

/-- Translation of the local line preserves its measure. -/
theorem localLine_translate_measurePreserving (shift : LocalLine) :
    MeasurePreserving (fun coordinates : LocalLine => coordinates + shift) localLineMeasure
      localLineMeasure := by
  unfold localLineMeasure
  exact (measurePreserving_add_right (volume : Measure ℝ) shift.1).prod
    (measurePreserving_add_right normalizedLocalThreeMeasure shift.2)

/-- Translation of the local line radical preserves its measure. -/
theorem localRadical_translate_measurePreserving (shift : LocalLine × LocalLine) :
    MeasurePreserving (fun coordinates : LocalLine × LocalLine => coordinates + shift)
      localRadicalMeasure localRadicalMeasure :=
  (localLine_translate_measurePreserving shift.1).prod
    (localLine_translate_measurePreserving shift.2)

theorem localRadical_add (first second : LocalLine × LocalLine) :
    localRadical (first + second) = localRadical first * localRadical second := by
  unfold localRadical
  rw [Prod.fst_add, Prod.snd_add, localAdele_add, localAdele_add, lineUnipotent_add]

theorem localIntegrand_localRadical {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (shift : LocalLine × LocalLine) (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter function induced (localRadical shift * argument) coordinates =
      localIntegrand data parameter function induced argument (coordinates + shift) := by
  unfold localIntegrand
  rw [localRadical_add]
  simp only [mul_assoc]

/-- The local standard integral is invariant under left translation of the argument by the local
line radical. -/
theorem localValue_localRadical {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (shift : LocalLine × LocalLine) (argument : AdelicGL) :
    localValue data parameter function induced (localRadical shift * argument) =
      localValue data parameter function induced argument := by
  unfold localValue
  simp_rw [localIntegrand_localRadical]
  exact (localRadical_translate_measurePreserving shift).integral_comp
    (Homeomorph.addRight shift).measurableEmbedding
    (fun coordinates => localIntegrand data parameter function induced argument coordinates)

end TernaryPeriodPolynomials.EdgeConvergence
