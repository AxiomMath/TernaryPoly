module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SectionSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.Equivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations

@[expose] public section


/-!
# Eisenstein values and section spaces from absolute convergence

Convergent counterparts of `StandardConstruction.{EisensteinValue, RationalEisenstein,
SectionSpace, CompactEquivariance, FlatUniqueness}`.  Only the declarations that depend on the
continuation hypothesis `PlaneEisensteinHolomorphic` are re-stated here, with
`PlaneEisensteinConvergent` in its place; the value of the Eisenstein series at the cohomological
point is the sum `∑' flag, F s₀ (γ_flag⁻¹ g)` itself (not a chosen meromorphic continuation), so
linearity and the invariance properties are `tsum` computations.

Re-port of the Sol reference implementation (via `Proofs/AxiomCodeGraph/StandardConstruction`) by Claude Sonnet 5.5; proofs of the continuation-dependent lemmas rewritten,
the others textually as in the source.
-/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein

open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

namespace EisensteinValue

/-- The sum of the plane Eisenstein series of a flat family at the cohomological point.  Its
linearity follows from absolute convergence there (CF3). -/
def eisensteinValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    StandardConstruction.EisensteinValue.flatFamilies data →ₗ[ℂ] (AdelicGL → ℂ) where
  toFun extension argument :=
    ∑' flag : Flags .plane, eisensteinSummand extension.val cohomologicalPoint argument flag
  map_add' first second := by
    funext argument
    change ∑' flag : Flags .plane, (eisensteinSummand first.val cohomologicalPoint argument flag +
        eisensteinSummand second.val cohomologicalPoint argument flag) =
      (∑' flag : Flags .plane, eisensteinSummand first.val cohomologicalPoint argument flag) +
        ∑' flag : Flags .plane, eisensteinSummand second.val cohomologicalPoint argument flag
    exact (summable_cohomological holomorphic first.val first.property argument).tsum_add
      (summable_cohomological holomorphic second.val second.property argument)
  map_smul' scalar extension := by
    funext argument
    change ∑' flag : Flags .plane, scalar *
        eisensteinSummand extension.val cohomologicalPoint argument flag =
      scalar * ∑' flag : Flags .plane,
        eisensteinSummand extension.val cohomologicalPoint argument flag
    exact tsum_mul_left

theorem eisensteinValue_apply {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (extension : StandardConstruction.EisensteinValue.flatFamilies data) (argument : AdelicGL) :
    eisensteinValue data holomorphic extension argument =
      ∑' flag : Flags .plane,
        eisensteinSummand extension.val cohomologicalPoint argument flag := rfl

end EisensteinValue

namespace RationalEisenstein

theorem eisensteinValue_rational {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (extension : StandardConstruction.EisensteinValue.flatFamilies data) (element : RationalGL3)
    (argument : AdelicGL) :
    EisensteinValue.eisensteinValue data holomorphic extension
        (rationalGroup element * argument) =
      EisensteinValue.eisensteinValue data holomorphic extension argument := by
  rw [EisensteinValue.eisensteinValue_apply, EisensteinValue.eisensteinValue_apply]
  have reindexed : ∀ flag : Flags .plane,
      eisensteinSummand extension.val cohomologicalPoint (rationalGroup element * argument) flag =
        eisensteinSummand extension.val cohomologicalPoint argument (element⁻¹ • flag) :=
    fun flag => StandardConstruction.RationalEisenstein.eisensteinSummand_rational data
      extension.val cohomologicalPoint (extension.property.1 cohomologicalPoint) element
      argument flag
  rw [tsum_congr reindexed]
  exact (MulAction.toPerm element⁻¹).tsum_eq
    (eisensteinSummand extension.val cohomologicalPoint argument)

theorem eisensteinValue_finite {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (extension : StandardConstruction.EisensteinValue.flatFamilies data)
    (levelElement : finiteLevel) (argument : AdelicGL) :
    EisensteinValue.eisensteinValue data holomorphic extension
        (argument * atFinite levelElement.val) =
      EisensteinValue.eisensteinValue data holomorphic extension argument := by
  rw [EisensteinValue.eisensteinValue_apply, EisensteinValue.eisensteinValue_apply]
  refine tsum_congr fun flag => ?_
  change extension.val cohomologicalPoint
      (rationalGroup flag.out⁻¹ * (argument * atFinite levelElement.val)) =
    extension.val cohomologicalPoint (rationalGroup flag.out⁻¹ * argument)
  rw [← mul_assoc, (extension.property.1 cohomologicalPoint).2.1 levelElement]

def automorphicEisensteinValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    StandardConstruction.EisensteinValue.flatFamilies data →ₗ[ℂ]
      StandardConstruction.RationalEisenstein.automorphicFunctions :=
  (EisensteinValue.eisensteinValue data holomorphic).codRestrict
    StandardConstruction.RationalEisenstein.automorphicFunctions
    (fun extension => ⟨eisensteinValue_rational data holomorphic extension,
      eisensteinValue_finite data holomorphic extension⟩)

end RationalEisenstein

namespace SectionSpace

theorem endpointEvaluation_surjective {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    Function.Surjective (StandardConstruction.SectionSpace.endpointEvaluation data) := by
  intro sectionValue
  obtain ⟨extension, flat, realizes⟩ := holomorphic.flat sectionValue.val sectionValue.property
  refine ⟨⟨extension, flat⟩, ?_⟩
  exact Subtype.ext realizes

theorem flatExtension_exists {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    ∃ extension : StandardConstruction.SectionSpace.inducedSections data .plane
        cohomologicalPoint →ₗ[ℂ] StandardConstruction.EisensteinValue.flatFamilies data,
      (StandardConstruction.SectionSpace.endpointEvaluation data).comp extension =
        LinearMap.id := by
  exact (StandardConstruction.SectionSpace.endpointEvaluation data).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (endpointEvaluation_surjective data holomorphic))

def linearFlatExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    StandardConstruction.SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      StandardConstruction.EisensteinValue.flatFamilies data :=
  Classical.choose (flatExtension_exists data holomorphic)

theorem linearFlatExtension_endpoint {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : StandardConstruction.SectionSpace.inducedSections data .plane
      cohomologicalPoint) :
    (linearFlatExtension data holomorphic sectionValue).val cohomologicalPoint =
      sectionValue.val := by
  have rightInverse := Classical.choose_spec (flatExtension_exists data holomorphic)
  exact congrArg Subtype.val (congrArg (fun operator => operator sectionValue) rightInverse)

def sectionEisensteinValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    StandardConstruction.SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      StandardConstruction.RationalEisenstein.automorphicFunctions :=
  (RationalEisenstein.automorphicEisensteinValue data holomorphic).comp
    (linearFlatExtension data holomorphic)

end SectionSpace

namespace FlatUniqueness

theorem linearFlatExtension_unique {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : StandardConstruction.SectionSpace.inducedSections data .plane
      cohomologicalPoint)
    (extension : StandardConstruction.EisensteinValue.flatFamilies data)
    (endpoint : extension.val cohomologicalPoint = sectionValue.val) :
    SectionSpace.linearFlatExtension data holomorphic sectionValue = extension := by
  apply Subtype.ext
  exact StandardConstruction.FlatUniqueness.flat_unique data _ _
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).property
    extension.property
    ((SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue).trans
      endpoint.symm)

end FlatUniqueness

namespace CompactEquivariance

theorem eisensteinValue_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (extension : StandardConstruction.EisensteinValue.flatFamilies data)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) (argument : AdelicGL) :
    EisensteinValue.eisensteinValue data holomorphic
      (RealTranslations.flatRightCompact data real orthogonal extension) argument =
        EisensteinValue.eisensteinValue data holomorphic extension
          (argument * atInfinity real) := by
  rw [EisensteinValue.eisensteinValue_apply, EisensteinValue.eisensteinValue_apply]
  refine tsum_congr fun flag => ?_
  exact congrFun (StandardConstruction.CompactEquivariance.eisensteinSummand_right
    extension.val cohomologicalPoint argument (atInfinity real)) flag

theorem linearFlatExtension_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : StandardConstruction.SectionSpace.inducedSections data .plane
      cohomologicalPoint)
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
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : StandardConstruction.SectionSpace.inducedSections data .plane
      cohomologicalPoint)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) (argument : AdelicGL) :
    (SectionSpace.sectionEisensteinValue data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val
        argument =
        (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val
          (argument * atInfinity real) := by
  change EisensteinValue.eisensteinValue data holomorphic
    (SectionSpace.linearFlatExtension data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue))
        argument =
        EisensteinValue.eisensteinValue data holomorphic
          (SectionSpace.linearFlatExtension data holomorphic sectionValue)
            (argument * atInfinity real)
  rw [linearFlatExtension_compact data holomorphic sectionValue real orthogonal,
    eisensteinValue_compact]

end CompactEquivariance

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein
