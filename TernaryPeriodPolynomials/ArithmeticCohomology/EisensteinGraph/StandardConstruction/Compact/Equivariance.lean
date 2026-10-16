module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Value

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactEquivariance

theorem eisensteinSummand_right (extension : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (argument right : AdelicGL) :
    eisensteinSummand (fun parameter argument => extension parameter (argument * right))
      parameter argument = eisensteinSummand extension parameter (argument * right) := by
  funext flag
  exact congrArg (extension parameter) (mul_assoc _ _ _)

theorem standardIntegrand_right (extension : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (argument right : AdelicGL) :
    standardIntegrand (fun parameter argument => extension parameter (argument * right))
      parameter argument = standardIntegrand extension parameter (argument * right) := by
  funext coordinates
  exact congrArg (extension parameter) (mul_assoc _ _ _)

theorem eisensteinContinuation_right (extension continuation : ℂ → AdelicGL → ℂ)
    (continues : IsEisensteinContinuation extension continuation) (right : AdelicGL) :
    IsEisensteinContinuation (fun parameter argument => extension parameter (argument * right))
      (fun parameter argument => continuation parameter (argument * right)) := by
  refine ⟨fun argument parameter => continues.1 (argument * right) parameter, ?_⟩
  obtain ⟨threshold, sums⟩ := continues.2
  refine ⟨threshold, ?_⟩
  intro parameter membership argument
  rw [eisensteinSummand_right]
  exact sums parameter membership (argument * right)

theorem standardContinuation_right (extension continuation : ℂ → AdelicGL → ℂ)
    (continues : IsStandardContinuation extension continuation) (right : AdelicGL) :
    IsStandardContinuation (fun parameter argument => extension parameter (argument * right))
      (fun parameter argument => continuation parameter (argument * right)) := by
  refine ⟨fun argument parameter => continues.1 (argument * right) parameter, ?_⟩
  obtain ⟨threshold, integrals⟩ := continues.2
  refine ⟨threshold, ?_⟩
  intro parameter membership argument
  rw [standardIntegrand_right]
  exact integrals parameter membership (argument * right)

theorem hasRegularStandard_right (extension : ℂ → AdelicGL → ℂ)
    (regular : StandardValue.HasRegularStandard extension) (right : AdelicGL) :
    StandardValue.HasRegularStandard (fun parameter argument => extension parameter (argument * right)) := by
  obtain ⟨continuation, continues, analytic⟩ := regular
  exact ⟨fun parameter argument => continuation parameter (argument * right),
    standardContinuation_right extension continuation continues right,
    fun argument => analytic (argument * right)⟩

theorem eisensteinValue_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (extension : EisensteinValue.flatFamilies data)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) (argument : AdelicGL) :
    EisensteinValue.eisensteinValue data holomorphic
      (RealTranslations.flatRightCompact data real orthogonal extension) argument =
        EisensteinValue.eisensteinValue data holomorphic extension (argument * atInfinity real) := by
  have spec := EisensteinValue.chosenContinuation_spec data holomorphic extension
  exact congrFun (EisensteinValue.eisensteinValue_realizes data holomorphic
    (RealTranslations.flatRightCompact data real orthogonal extension)
    (fun parameter argument => EisensteinValue.chosenContinuation data holomorphic extension
      parameter (argument * atInfinity real))
    (eisensteinContinuation_right extension.val _ spec.1 (atInfinity real))
    (fun argument => spec.2 (argument * atInfinity real))) argument

theorem linearFlatExtension_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) :
    SectionSpace.linearFlatExtension data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue) =
        RealTranslations.flatRightCompact data real orthogonal
          (SectionSpace.linearFlatExtension data holomorphic sectionValue) := by
  apply FlatUniqueness.linearFlatExtension_unique
  funext argument
  exact congrFun (SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue)
    (argument * atInfinity real)

theorem sectionEisensteinValue_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) (argument : AdelicGL) :
    (SectionSpace.sectionEisensteinValue data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val argument =
        (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val
          (argument * atInfinity real) := by
  change EisensteinValue.eisensteinValue data holomorphic
    (SectionSpace.linearFlatExtension data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)) argument =
        EisensteinValue.eisensteinValue data holomorphic
          (SectionSpace.linearFlatExtension data holomorphic sectionValue) (argument * atInfinity real)
  rw [linearFlatExtension_compact data holomorphic sectionValue real orthogonal,
    eisensteinValue_compact]

def regularRightCompact {degree : ℕ} (data : InducingData degree)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) :
    Module.End ℂ (StandardValue.regularFamilies data) where
  toFun extension := ⟨RealTranslations.flatRightCompact data real orthogonal extension.val,
    hasRegularStandard_right extension.val.val extension.property (atInfinity real)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem standardValue_compact {degree : ℕ} (data : InducingData degree)
    (extension : StandardValue.regularFamilies data)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) (argument : AdelicGL) :
    StandardValue.standardValue data (regularRightCompact data real orthogonal extension) argument =
      StandardValue.standardValue data extension (argument * atInfinity real) := by
  have spec := StandardValue.chosenContinuation_spec data extension
  exact congrFun (StandardValue.standardValue_realizes data
    (regularRightCompact data real orthogonal extension)
    (fun parameter argument => StandardValue.chosenContinuation data extension
      parameter (argument * atInfinity real))
    (standardContinuation_right extension.val.val _ spec.1 (atInfinity real))
    (fun argument => spec.2 (argument * atInfinity real))) argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactEquivariance
