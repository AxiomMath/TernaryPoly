module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.PolynomialStandard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FamilyHilbertIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Relation

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointSourceStandard

theorem sectionFamily_hasSmoothCuspLift {degree arity : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (function vertices))
    (lift : HasSmoothCuspLift data .plane cohomologicalPoint function) :
    HasSmoothCuspLift data .line cohomologicalPoint (fun vertices =>
      (EndpointStandardValue.sectionStandard data large holomorphic ⟨function vertices, induced vertices⟩).val) := by
  let halfPlane := HilbertCohomological.point_in_halfPlane degree large
  intro argument
  refine ⟨fun real => HilbertStandardSmooth.vector data cohomologicalPoint
    (function (fun index => real index.castSucc)) (induced _) halfPlane
    (argument * atInfinity (real (Fin.last arity))), ?_, ?_⟩
  · exact FamilyHilbertIntegral.joint_smooth data cohomologicalPoint function induced lift halfPlane argument
  · intro real binary
    dsimp only
    rw [EndpointStandardValue.sectionStandard_eq_integral]
    let sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint :=
      ⟨function (fun index => real index.castSucc), induced _⟩
    let extension := SectionSpace.linearFlatExtension data holomorphic sectionValue
    have endpoint : extension.val cohomologicalPoint = function (fun index => real index.castSucc) :=
      SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue
    have realization := HilbertFullRealization.value_realizes_normalized data extension.val extension.property
      cohomologicalPoint halfPlane (argument * atInfinity (real (Fin.last arity))) binary
    simpa only [standardIntegrand, endpoint, binaryLevi] using realization

theorem sourceValue_isSource {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane) :
    IsSourceCocycle data .line (EndpointPolynomialStandard.sourceValue data large holomorphic source) := by
  refine ⟨?_, ?_, EndpointPolynomialStandard.sourceValue_real_covariant data large holomorphic source,
    EndpointPolynomialStandard.sourceValue_closed data large holomorphic source⟩
  · intro vertices monomial
    exact EndpointPolynomialStandard.polynomialValue_induced data large holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro monomial
    have lift := sectionFamily_hasSmoothCuspLift data large holomorphic
      (fun vertices argument => (source.val vertices argument).val.coeff monomial)
      (fun vertices => source.property.1 vertices monomial) (source.property.2.1 monomial)
    simp only [EndpointPolynomialStandard.sourceValue, EndpointPolynomialStandard.polynomialValue_coeff]
    exact lift

def sourceCocycle {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane) :
    SourceSpace.sourceCocycles data .line :=
  ⟨EndpointPolynomialStandard.sourceValue data large holomorphic source,
    sourceValue_isSource data large holomorphic source⟩

def sourceStandard {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    SourceSpace.sourceCocycles data .plane →ₗ[ℂ] SourceSpace.sourceCocycles data .line where
  toFun := sourceCocycle data large holomorphic
  map_add' first second := by
    apply Subtype.ext
    funext vertices argument
    change EndpointPolynomialStandard.polynomialValue data large holomorphic
      (PolynomialEisenstein.sourceSection data first vertices + PolynomialEisenstein.sourceSection data second vertices) argument = _
    rw [map_add]
    rfl
  map_smul' scalar source := by
    apply Subtype.ext
    funext vertices argument
    change EndpointPolynomialStandard.polynomialValue data large holomorphic
      (scalar • PolynomialEisenstein.sourceSection data source vertices) argument = _
    rw [map_smul]
    rfl

theorem sourceStandard_related {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane) :
    StandardRelation.Related data source (sourceStandard data large holomorphic source) := by
  refine ⟨PolynomialFamilies.sourceFlatExtension data holomorphic source,
    EndpointPolynomialStandard.sourceContinuation data large holomorphic source, ?_,
    PolynomialFamilies.sourceFlatExtension_endpoint data holomorphic source, ?_, ?_, rfl⟩
  · intro vertices monomial
    exact PolynomialFamilies.polynomialFlatExtension_flat data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro vertices monomial
    exact EndpointPolynomialStandard.polynomialContinuation_continues data large holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro vertices argument monomial
    exact EndpointPolynomialStandard.polynomialContinuation_regular data large holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) argument monomial

theorem related_total {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    ∀ plane : SourceSpace.sourceCocycles data .plane, ∃ line, StandardRelation.Related data plane line := by
  intro plane
  exact ⟨sourceStandard data large holomorphic plane, sourceStandard_related data large holomorphic plane⟩

theorem planeClass_surjective {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    Function.Surjective (StandardRelation.planeClass data) :=
  StandardRelation.planeClass_surjective data (related_total data large holomorphic)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointSourceStandard
