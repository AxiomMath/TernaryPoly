module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceQuotient

instance sourceAddCommGroup {degree : ℕ} (data : InducingData degree) (side : Side) :
    AddCommGroup (SourceSpace.sourceCocycles data side) :=
  @Submodule.addCommGroup ℂ
    ((Fin 3 → RealGL3) → GeneralEisenstein.Adelic.AdelicGL → HomogeneousPoly degree)
    inferInstance inferInstance inferInstance (SourceSpace.sourceCocycles data side)

def sourceToSummand {degree : ℕ} (data : InducingData degree) (side : Side) :
    SourceSpace.sourceCocycles data side →ₗ[ℂ] boundarySummand data side :=
  (SourceSpace.sourceClass data side).codRestrict (boundarySummand data side)
    (fun source => by
      rw [← SourceSpace.sourceClass_range data side]
      exact ⟨source, rfl⟩)

theorem sourceToSummand_surjective {degree : ℕ} (data : InducingData degree)
    (side : Side) : Function.Surjective (sourceToSummand data side) := by
  intro cohomologyClass
  obtain ⟨source, realizes⟩ := SourceSpace.boundarySummand_representative data side
    cohomologyClass
  exact ⟨source, Subtype.ext realizes⟩

def sourceRelations {degree : ℕ} (data : InducingData degree) (side : Side) :
    Submodule ℂ (SourceSpace.sourceCocycles data side) :=
  LinearMap.ker (sourceToSummand data side)

def sourceQuotientEquiv {degree : ℕ} (data : InducingData degree) (side : Side) :
    (SourceSpace.sourceCocycles data side ⧸ sourceRelations data side) ≃ₗ[ℂ]
      boundarySummand data side :=
  (sourceToSummand data side).quotKerEquivOfSurjective
    (sourceToSummand_surjective data side)

theorem sourceQuotientEquiv_mk {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceSpace.sourceCocycles data side) :
    sourceQuotientEquiv data side (Submodule.Quotient.mk source) =
      sourceToSummand data side source :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

def descendSourceMap {degree : ℕ} (data : InducingData degree)
    (sourceOperator : SourceSpace.sourceCocycles data .plane →ₗ[ℂ]
      SourceSpace.sourceCocycles data .line)
    (respectsRelations : sourceRelations data .plane ≤
      LinearMap.ker ((sourceToSummand data .line).comp sourceOperator)) :
    boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line :=
  ((sourceRelations data .plane).liftQ
    ((sourceToSummand data .line).comp sourceOperator) respectsRelations).comp
      (sourceQuotientEquiv data .plane).symm.toLinearMap

theorem descendSourceMap_source {degree : ℕ} (data : InducingData degree)
    (sourceOperator : SourceSpace.sourceCocycles data .plane →ₗ[ℂ]
      SourceSpace.sourceCocycles data .line)
    (respectsRelations : sourceRelations data .plane ≤
      LinearMap.ker ((sourceToSummand data .line).comp sourceOperator))
    (source : SourceSpace.sourceCocycles data .plane) :
    descendSourceMap data sourceOperator respectsRelations
        (sourceToSummand data .plane source) =
      sourceToSummand data .line (sourceOperator source) := by
  exact (LinearMap.comp_apply _ _ _).trans
    ((congrArg ((sourceRelations data .plane).liftQ
      ((sourceToSummand data .line).comp sourceOperator) respectsRelations)
      ((LinearEquiv.symm_apply_eq _).mpr (sourceQuotientEquiv_mk data .plane source).symm)).trans
      (Submodule.liftQ_apply _ _ _))

theorem descendSourceMap_unique {degree : ℕ} (data : InducingData degree)
    (sourceOperator : SourceSpace.sourceCocycles data .plane →ₗ[ℂ]
      SourceSpace.sourceCocycles data .line)
    (respectsRelations : sourceRelations data .plane ≤
      LinearMap.ker ((sourceToSummand data .line).comp sourceOperator))
    (alternative : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (realizes : ∀ source, alternative (sourceToSummand data .plane source) =
      sourceToSummand data .line (sourceOperator source)) :
    alternative = descendSourceMap data sourceOperator respectsRelations := by
  apply LinearMap.ext
  intro cohomologyClass
  have surjective := sourceToSummand_surjective data .plane cohomologyClass
  obtain ⟨source, rfl⟩ := surjective
  exact (realizes source).trans
    (descendSourceMap_source data sourceOperator respectsRelations source).symm

theorem sourceMap_descends_iff {degree : ℕ} (data : InducingData degree)
    (sourceOperator : SourceSpace.sourceCocycles data .plane →ₗ[ℂ]
      SourceSpace.sourceCocycles data .line) :
    (∃ operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line,
      ∀ source, operator (sourceToSummand data .plane source) =
        sourceToSummand data .line (sourceOperator source)) ↔
      sourceRelations data .plane ≤
        LinearMap.ker ((sourceToSummand data .line).comp sourceOperator) := by
  constructor
  · rintro ⟨operator, realizes⟩ source relation
    exact LinearMap.mem_ker.mpr ((realizes source).symm.trans
      ((congrArg operator (LinearMap.mem_ker.mp relation)).trans (map_zero operator)))
  · intro respectsRelations
    exact ⟨descendSourceMap data sourceOperator respectsRelations,
      descendSourceMap_source data sourceOperator respectsRelations⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceQuotient
