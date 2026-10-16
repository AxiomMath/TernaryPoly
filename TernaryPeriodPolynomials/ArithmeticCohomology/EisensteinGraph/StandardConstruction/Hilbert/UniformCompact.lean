module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.FixedStandard

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertUniformCompact

def normalizedValue {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) : data.cusp.H :=
  normPower (GeneralLinearGroup.det binary)
    (-binaryInductionExponent degree .line parameter) •
      HilbertStandard.value data parameter function induced (lineLevi 1 binary * argument)

theorem normalizedValue_eq_action {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    normalizedValue data parameter function induced binary argument =
      data.cusp.π binary (HilbertStandard.value data parameter function induced argument) := by
  have cancel : normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .line parameter) *
        normPower (GeneralLinearGroup.det binary)
          (binaryInductionExponent degree .line parameter) = 1 := by
    simpa only [mul_one] using ParabolicInvariance.normPower_neg_mul
      (GeneralLinearGroup.det binary) (binaryInductionExponent degree .line parameter) (1 : ℂ)
  unfold normalizedValue
  rw [HilbertBinaryCovariance.value_lineLevi, smul_smul, cancel, one_smul]

theorem normalizedValue_norm {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    ‖normalizedValue data parameter function induced binary argument‖ =
      ‖HilbertStandard.value data parameter function induced argument‖ := by
  rw [normalizedValue_eq_action]
  exact data.cusp.unitary binary _

theorem flatValue_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Continuous (fun argument => HilbertStandard.value data parameter
      (extension parameter) (flat.1 parameter) argument) := by
  apply continuous_iff_continuousAt.mpr
  intro argument
  exact ContinuousAt.comp'
    (f := fun argument : AdelicGL => (parameter, argument))
    (g := fun pair : ℂ × AdelicGL => HilbertStandard.value data pair.1
      (extension pair.1) (flat.1 pair.1) pair.2)
    (x := argument)
    (HilbertTruncation.standard_joint_continuousAt data extension flat parameter
      argument halfPlane) (continuous_const.prodMk continuous_id).continuousAt

theorem flatValue_uniform {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    ∃ bound : ℝ, ∀ argument, inMaximalCompact argument →
      ∀ binary : BinaryAdelicGL,
        ‖normalizedValue data parameter (extension parameter)
          (flat.1 parameter) binary argument‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := MaximalCompact.isCompact.exists_bound_of_continuousOn
    (flatValue_continuous data extension flat parameter halfPlane).continuousOn
  refine ⟨bound, ?_⟩
  intro argument membership binary
  rw [normalizedValue_norm]
  exact bounded argument membership

theorem cohomologicalValue_continuous {degree : ℕ} (data : InducingData degree)
    (atLeastFour : 4 ≤ degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    Continuous (HilbertCohomological.valueLinear data atLeastFour sectionValue) := by
  let extension := SectionSpace.linearFlatExtension data holomorphic sectionValue
  have endpoint :
      (⟨extension.val cohomologicalPoint, extension.property.1 cohomologicalPoint⟩ :
        SectionSpace.inducedSections data .plane cohomologicalPoint) = sectionValue :=
    Subtype.ext (SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue)
  change Continuous (HilbertStandard.value data cohomologicalPoint
    sectionValue.val sectionValue.property)
  rw [← endpoint]
  exact flatValue_continuous data extension.val extension.property cohomologicalPoint
    (HilbertCohomological.point_in_halfPlane degree atLeastFour)

theorem cohomologicalValue_uniform {degree : ℕ} (data : InducingData degree)
    (atLeastFour : 4 ≤ degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    ∃ bound : ℝ, ∀ argument, inMaximalCompact argument →
      ∀ binary : BinaryAdelicGL,
        ‖normPower (GeneralLinearGroup.det binary)
          (-binaryInductionExponent degree .line cohomologicalPoint) •
            HilbertCohomological.valueLinear data atLeastFour sectionValue
              (lineLevi 1 binary * argument)‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := MaximalCompact.isCompact.exists_bound_of_continuousOn
    (cohomologicalValue_continuous data atLeastFour holomorphic sectionValue).continuousOn
  refine ⟨bound, ?_⟩
  intro argument membership binary
  have induced : IsInduced data .plane cohomologicalPoint sectionValue.val :=
    sectionValue.property
  change ‖normalizedValue data cohomologicalPoint sectionValue.val
    induced binary argument‖ ≤ bound
  rw [normalizedValue_norm]
  exact bounded argument membership

theorem cohomologicalValue_uniform_rightReal {degree : ℕ} (data : InducingData degree)
    (atLeastFour : 4 ≤ degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (realSet : Set RealGL3) (realCompact : IsCompact realSet) :
    ∃ bound : ℝ, ∀ argument, inMaximalCompact argument →
      ∀ real ∈ realSet, ∀ binary : BinaryAdelicGL,
        ‖normPower (GeneralLinearGroup.det binary)
          (-binaryInductionExponent degree .line cohomologicalPoint) •
            HilbertCohomological.valueLinear data atLeastFour sectionValue
              (lineLevi 1 binary * (argument * atInfinity real))‖ ≤ bound := by
  let translated : Set AdelicGL :=
    (fun pair : AdelicGL × RealGL3 => pair.1 * atInfinity pair.2) ''
      ({argument | inMaximalCompact argument} ×ˢ realSet)
  have translatedCompact : IsCompact translated :=
    (MaximalCompact.isCompact.prod realCompact).image
      (continuous_fst.mul (HilbertFixedStandard.atInfinity_continuous.comp continuous_snd))
  obtain ⟨bound, bounded⟩ := translatedCompact.exists_bound_of_continuousOn
    (cohomologicalValue_continuous data atLeastFour holomorphic sectionValue).continuousOn
  refine ⟨bound, ?_⟩
  intro argument membership real realMembership binary
  change ‖normalizedValue data cohomologicalPoint sectionValue.val
    (show IsInduced data .plane cohomologicalPoint sectionValue.val from sectionValue.property)
    binary (argument * atInfinity real)‖ ≤ bound
  rw [normalizedValue_norm]
  exact bounded (argument * atInfinity real)
    ⟨(argument, real), ⟨membership, realMembership⟩, rfl⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertUniformCompact
