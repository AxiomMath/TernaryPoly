module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceQuotient
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Value

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardRelation

def Related {degree : ℕ} (data : InducingData degree)
    (plane : SourceSpace.sourceCocycles data .plane)
    (line : SourceSpace.sourceCocycles data .line) : Prop :=
  ∃ extension continuation :
      ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree,
    (∀ vertices monomial, IsFlatSection data (fun parameter argument =>
      (extension parameter vertices argument).val.coeff monomial)) ∧
    extension cohomologicalPoint = plane.val ∧
    (∀ vertices monomial, IsStandardContinuation
      (fun parameter argument =>
        (extension parameter vertices argument).val.coeff monomial)
      (fun parameter argument =>
        (continuation parameter vertices argument).val.coeff monomial)) ∧
    (∀ vertices argument monomial, AnalyticAt ℂ (fun parameter =>
      (continuation parameter vertices argument).val.coeff monomial)
      cohomologicalPoint) ∧
    continuation cohomologicalPoint = line.val

theorem related_zero {degree : ℕ} (data : InducingData degree) :
    Related data 0 0 := by
  refine ⟨0, 0, ?_, rfl, ?_, ?_, rfl⟩
  · intro vertices monomial
    simpa only [Pi.zero_apply, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      FlatExtensions.flat_zero data
  · intro vertices monomial
    simpa only [Pi.zero_apply, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      FlatExtensions.standardContinuation_zero
  · intro vertices argument monomial
    simpa only [Pi.zero_apply, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) cohomologicalPoint)

theorem related_add {degree : ℕ} (data : InducingData degree)
    (firstPlane secondPlane : SourceSpace.sourceCocycles data .plane)
    (firstLine secondLine : SourceSpace.sourceCocycles data .line)
    (firstRelated : Related data firstPlane firstLine)
    (secondRelated : Related data secondPlane secondLine) :
    Related data (firstPlane + secondPlane) (firstLine + secondLine) := by
  obtain ⟨firstExtension, firstContinuation, firstFlat, firstEndpoint,
    firstContinues, firstRegular, firstValue⟩ := firstRelated
  obtain ⟨secondExtension, secondContinuation, secondFlat, secondEndpoint,
    secondContinues, secondRegular, secondValue⟩ := secondRelated
  refine ⟨firstExtension + secondExtension, firstContinuation + secondContinuation,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro vertices monomial
    simpa only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      LinearFamilies.flat_add data _ _ (firstFlat vertices monomial)
        (secondFlat vertices monomial)
  · change firstExtension cohomologicalPoint + secondExtension cohomologicalPoint = _
    rw [firstEndpoint, secondEndpoint]
    rfl
  · intro vertices monomial
    simpa only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      LinearFamilies.standardContinuation_add _ _ _ _
        (firstContinues vertices monomial) (secondContinues vertices monomial)
  · intro vertices argument monomial
    simp only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    convert (firstRegular vertices argument monomial).add
      (secondRegular vertices argument monomial) using 1
  · change firstContinuation cohomologicalPoint + secondContinuation cohomologicalPoint = _
    rw [firstValue, secondValue]
    rfl

theorem related_smul {degree : ℕ} (data : InducingData degree) (scalar : ℂ)
    (plane : SourceSpace.sourceCocycles data .plane)
    (line : SourceSpace.sourceCocycles data .line) (related : Related data plane line) :
    Related data (scalar • plane) (scalar • line) := by
  obtain ⟨extension, continuation, flat, endpoint, continues, regular, value⟩ := related
  refine ⟨scalar • extension, scalar • continuation, ?_, ?_, ?_, ?_, ?_⟩
  · intro vertices monomial
    simpa only [Pi.smul_apply, Submodule.coe_smul, MvPolynomial.coeff_smul,
      smul_eq_mul] using LinearFamilies.flat_smul data scalar _ (flat vertices monomial)
  · change scalar • extension cohomologicalPoint = _
    rw [endpoint]
    rfl
  · intro vertices monomial
    simpa only [Pi.smul_apply, Submodule.coe_smul, MvPolynomial.coeff_smul,
      smul_eq_mul] using LinearFamilies.standardContinuation_smul scalar _ _
        (continues vertices monomial)
  · intro vertices argument monomial
    simp only [Pi.smul_apply, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    convert (regular vertices argument monomial).const_smul (c := scalar) using 1
  · change scalar • continuation cohomologicalPoint = _
    rw [value]
    rfl

def sourceRelation {degree : ℕ} (data : InducingData degree) :
    Submodule ℂ (SourceSpace.sourceCocycles data .plane ×
      SourceSpace.sourceCocycles data .line) where
  carrier := {pair | Related data pair.1 pair.2}
  zero_mem' := related_zero data
  add_mem' {first second} firstRelated secondRelated :=
    related_add data first.1 second.1 first.2 second.2 firstRelated secondRelated
  smul_mem' scalar pair related := related_smul data scalar pair.1 pair.2 related

def planeClass {degree : ℕ} (data : InducingData degree) :
    sourceRelation data →ₗ[ℂ] boundarySummand data .plane :=
  (SourceQuotient.sourceToSummand data .plane).comp
    ((LinearMap.fst ℂ _ _).comp (sourceRelation data).subtype)

def lineClass {degree : ℕ} (data : InducingData degree) :
    sourceRelation data →ₗ[ℂ] boundarySummand data .line :=
  (SourceQuotient.sourceToSummand data .line).comp
    ((LinearMap.snd ℂ _ _).comp (sourceRelation data).subtype)

theorem planeClass_surjective {degree : ℕ} (data : InducingData degree)
    (existsIntegral : ∀ plane : SourceSpace.sourceCocycles data .plane,
      ∃ line, Related data plane line) : Function.Surjective (planeClass data) := by
  intro cohomologyClass
  obtain ⟨plane, realizes⟩ :=
    SourceQuotient.sourceToSummand_surjective data .plane cohomologyClass
  have integral := existsIntegral plane
  obtain ⟨line, related⟩ := integral
  exact ⟨⟨(plane, line), related⟩, realizes⟩

def descendedStandard {degree : ℕ} (data : InducingData degree)
    (existsIntegral : ∀ plane : SourceSpace.sourceCocycles data .plane,
      ∃ line, Related data plane line)
    (respectsRelations : LinearMap.ker (planeClass data) ≤ LinearMap.ker (lineClass data)) :
    boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line :=
  ((LinearMap.ker (planeClass data)).liftQ (lineClass data) respectsRelations).comp
    ((planeClass data).quotKerEquivOfSurjective
      (planeClass_surjective data existsIntegral)).symm.toLinearMap

theorem liftQ_quotKerEquiv_apply {Domain Target Result : Type}
    [AddCommGroup Domain] [Module ℂ Domain]
    [AddCommGroup Target] [Module ℂ Target]
    [AddCommGroup Result] [Module ℂ Result]
    (projection : Domain →ₗ[ℂ] Target) (surjective : Function.Surjective projection)
    (operator : Domain →ₗ[ℂ] Result)
    (respectsRelations : projection.ker ≤ operator.ker) (point : Domain) :
    projection.ker.liftQ operator respectsRelations
      ((projection.quotKerEquivOfSurjective surjective).symm (projection point)) =
        operator point := by
  rw [← LinearMap.quotKerEquivOfSurjective_apply_mk projection surjective point,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]

theorem descendedStandard_related {degree : ℕ} (data : InducingData degree)
    (existsIntegral : ∀ plane : SourceSpace.sourceCocycles data .plane,
      ∃ line, Related data plane line)
    (respectsRelations : LinearMap.ker (planeClass data) ≤ LinearMap.ker (lineClass data))
    (pair : sourceRelation data) :
    descendedStandard data existsIntegral respectsRelations (planeClass data pair) =
      lineClass data pair := by
  exact liftQ_quotKerEquiv_apply (planeClass data)
    (planeClass_surjective data existsIntegral) (lineClass data) respectsRelations pair

theorem realizesStandard_iff {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) :
    RealizesStandard data standard ↔
      ∀ plane : SourceSpace.sourceCocycles data .plane, ∃ line,
        Related data plane line ∧
        standard (SourceQuotient.sourceToSummand data .plane plane) =
          SourceQuotient.sourceToSummand data .line line := by
  constructor
  · intro realizes plane
    have realized := realizes plane.val plane.property
        (SourceSpace.evaluatedSource data .plane plane)
        (SourceSpace.evaluatedSource_realizes data .plane plane)
        (SourceQuotient.sourceToSummand data .plane plane).property
    obtain ⟨extension, continuation, flat, endpoint, continues, regular,
      source, representative, evaluates, value⟩ := realized
    let line : SourceSpace.sourceCocycles data .line :=
      ⟨continuation cohomologicalPoint, source⟩
    refine ⟨line, ⟨extension, continuation, flat, endpoint, continues, regular, rfl⟩, ?_⟩
    apply Subtype.ext
    change (standard (SourceQuotient.sourceToSummand data .plane plane)).val =
      SourceSpace.sourceClass data .line line
    have inputEquality : SourceQuotient.sourceToSummand data .plane plane =
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
          (SourceSpace.evaluatedSource data .plane plane),
          (SourceQuotient.sourceToSummand data .plane plane).property⟩ := by
      apply Subtype.ext
      rfl
    calc
      _ = (standard ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
          (SourceSpace.evaluatedSource data .plane plane),
          (SourceQuotient.sourceToSummand data .plane plane).property⟩).val :=
        congrArg (fun input => (standard input).val) inputEquality
      _ = classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
          representative := value
      _ = SourceSpace.sourceClass data .line line := by
        unfold SourceSpace.sourceClass
        simp only [LinearMap.comp_apply, SourceSpace.evaluationLinear]
        congr 1
        exact (SourceSpace.evaluates_unique data .line line.val _ _
          (SourceSpace.evaluatedSource_realizes data .line line) evaluates).symm
  · intro realizes source isSource representative evaluates membership
    let plane : SourceSpace.sourceCocycles data .plane := ⟨source, isSource⟩
    have realizedPlane := realizes plane
    obtain ⟨line, related, value⟩ := realizedPlane
    obtain ⟨extension, continuation, flat, endpoint, continues, regular, lineEndpoint⟩ := related
    have representativeEquality : representative = SourceSpace.evaluatedSource data .plane plane :=
      SourceSpace.evaluates_unique data .plane source _ _ evaluates
        (SourceSpace.evaluatedSource_realizes data .plane plane)
    subst representative
    refine ⟨extension, continuation, flat, endpoint, continues, regular, ?_,
      SourceSpace.evaluatedSource data .line line, ?_, ?_⟩
    · rw [lineEndpoint]
      exact line.property
    · rw [lineEndpoint]
      exact SourceSpace.evaluatedSource_realizes data .line line
    · exact congrArg Subtype.val value

theorem descendedStandard_realizes {degree : ℕ} (data : InducingData degree)
    (existsIntegral : ∀ plane : SourceSpace.sourceCocycles data .plane,
      ∃ line, Related data plane line)
    (respectsRelations : LinearMap.ker (planeClass data) ≤ LinearMap.ker (lineClass data)) :
    RealizesStandard data (descendedStandard data existsIntegral respectsRelations) := by
  apply (realizesStandard_iff data _).mpr
  intro plane
  have integral := existsIntegral plane
  obtain ⟨line, related⟩ := integral
  exact ⟨line, related,
    descendedStandard_related data existsIntegral respectsRelations ⟨(plane, line), related⟩⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardRelation
