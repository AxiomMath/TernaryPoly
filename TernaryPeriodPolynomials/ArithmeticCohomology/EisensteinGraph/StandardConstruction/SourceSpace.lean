module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.EisensteinValue

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace

theorem source_zero {degree : ℕ} (data : InducingData degree) (side : Side) :
    IsSourceCocycle data side (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro vertices monomial
    simpa only [Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      FlatExtensions.induced_zero data side cohomologicalPoint
  · intro monomial
    simpa only [Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      (FlatExtensions.smoothCuspLift_zero (count := 3) data side cohomologicalPoint)
  · intro element vertices argument
    exact (map_zero _).symm
  · intro vertices argument
    simp

theorem source_add {degree : ℕ} (data : InducingData degree) (side : Side)
    (first second : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (firstSource : IsSourceCocycle data side first)
    (secondSource : IsSourceCocycle data side second) :
    IsSourceCocycle data side
      (fun vertices argument => first vertices argument + second vertices argument) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro vertices monomial
    simpa only [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      LinearFamilies.induced_add data side cohomologicalPoint _ _
        (firstSource.1 vertices monomial) (secondSource.1 vertices monomial)
  · intro monomial
    simpa only [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      LinearFamilies.smoothCuspLift_add data side cohomologicalPoint _ _
        (firstSource.2.1 monomial) (secondSource.2.1 monomial)
  · intro element vertices argument
    change first _ _ + second _ _ =
      realCoefficientComponent degree data.chi element (first _ _ + second _ _)
    rw [firstSource.2.2.1, secondSource.2.2.1, map_add]
  · intro vertices argument
    have firstClosed := firstSource.2.2.2 vertices argument
    have secondClosed := secondSource.2.2.2 vertices argument
    calc
      _ = (first ![vertices 1, vertices 2, vertices 3] argument -
          first ![vertices 0, vertices 2, vertices 3] argument +
          first ![vertices 0, vertices 1, vertices 3] argument -
          first ![vertices 0, vertices 1, vertices 2] argument) +
        (second ![vertices 1, vertices 2, vertices 3] argument -
          second ![vertices 0, vertices 2, vertices 3] argument +
          second ![vertices 0, vertices 1, vertices 3] argument -
          second ![vertices 0, vertices 1, vertices 2] argument) := by
            dsimp only
            abel
      _ = 0 := by rw [firstClosed, secondClosed, add_zero]

theorem source_smul {degree : ℕ} (data : InducingData degree) (side : Side)
    (scalar : ℂ) (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) :
    IsSourceCocycle data side (fun vertices argument => scalar • source vertices argument) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro vertices monomial
    simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
      LinearFamilies.induced_smul data side cohomologicalPoint scalar _
        (isSource.1 vertices monomial)
  · intro monomial
    simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
      LinearFamilies.smoothCuspLift_smul data side cohomologicalPoint scalar _
        (isSource.2.1 monomial)
  · intro element vertices argument
    change scalar • source _ _ =
      realCoefficientComponent degree data.chi element (scalar • source _ _)
    rw [isSource.2.2.1, map_smul]
  · intro vertices argument
    simpa only [smul_sub, smul_add, smul_zero] using
      congrArg (fun polynomial => scalar • polynomial) (isSource.2.2.2 vertices argument)

def sourceCocycles {degree : ℕ} (data : InducingData degree) (side : Side) :
    Submodule ℂ ((Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree) where
  carrier := {source | IsSourceCocycle data side source}
  zero_mem' := source_zero data side
  add_mem' {first second} firstSource secondSource :=
    source_add data side first second firstSource secondSource
  smul_mem' scalar source isSource := source_smul data side scalar source isSource

def evaluatedSource {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : sourceCocycles data side) :
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi)
      side) :=
  Comparison.evaluatedCocycle data side source.val source.property
    (RationalComparison.source_flagIndependent data RationalNorm.rational_norm
      side source.val source.property)

theorem evaluatedSource_realizes {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : sourceCocycles data side) :
    Evaluates data side source.val (evaluatedSource data side source) :=
  Comparison.evaluatedCocycle_realizes data side source.val source.property _

theorem evaluates_unique {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (first second : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) side))
    (firstEvaluates : Evaluates data side source first)
    (secondEvaluates : Evaluates data side source second) : first = second := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices flag
  induction flag using Quotient.inductionOn with
  | h representative =>
    exact (firstEvaluates vertices representative).trans
      (secondEvaluates vertices representative).symm

def evaluationLinear {degree : ℕ} (data : InducingData degree) (side : Side) :
    sourceCocycles data side →ₗ[ℂ]
      cocycles rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) side) where
  toFun := evaluatedSource data side
  map_add' first second := by
    apply evaluates_unique data side (first + second).val
    · exact evaluatedSource_realizes data side (first + second)
    · intro vertices representative
      change (evaluatedSource data side first).val.val vertices (QuotientGroup.mk representative) +
        (evaluatedSource data side second).val.val vertices (QuotientGroup.mk representative) = _
      rw [evaluatedSource_realizes, evaluatedSource_realizes]
      rfl
  map_smul' scalar source := by
    apply evaluates_unique data side (scalar • source).val
    · exact evaluatedSource_realizes data side (scalar • source)
    · intro vertices representative
      change scalar • (evaluatedSource data side source).val.val vertices
        (QuotientGroup.mk representative) = _
      rw [evaluatedSource_realizes]
      rfl

def sourceClass {degree : ℕ} (data : InducingData degree) (side : Side) :
    sourceCocycles data side →ₗ[ℂ] StratumH2 degree data.chi side :=
  (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi)
    side)).comp (evaluationLinear data side)

theorem sourceClass_range {degree : ℕ} (data : InducingData degree) (side : Side) :
    LinearMap.range (sourceClass data side) = boundarySummand data side := by
  apply le_antisymm
  · rintro cohomologyClass ⟨source, rfl⟩
    apply Submodule.subset_span
    exact ⟨source.val, source.property, evaluatedSource data side source,
      evaluatedSource_realizes data side source, rfl⟩
  · apply Submodule.span_le.mpr
    rintro cohomologyClass ⟨source, isSource, representative, evaluates, rfl⟩
    refine ⟨⟨source, isSource⟩, ?_⟩
    change classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) side)
        (evaluatedSource data side ⟨source, isSource⟩) =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) side) representative
    congr 1
    exact evaluates_unique data side source _ _
      (evaluatedSource_realizes data side ⟨source, isSource⟩) evaluates

theorem boundarySummand_representative {degree : ℕ} (data : InducingData degree)
    (side : Side) (cohomologyClass : boundarySummand data side) :
    ∃ source : sourceCocycles data side,
      sourceClass data side source = cohomologyClass.val := by
  have membership : cohomologyClass.val ∈ LinearMap.range (sourceClass data side) := by
    simpa only [sourceClass_range data side] using cohomologyClass.property
  exact membership

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
