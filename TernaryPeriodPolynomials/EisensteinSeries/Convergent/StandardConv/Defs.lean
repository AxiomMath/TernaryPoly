module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Relation

@[expose] public section


/-!
# Standard realization with a half-plane continuation

`IsStandardContinuation F J` asks the standard family `J` to be meromorphic on the whole plane,
which is what the meromorphic continuation of the standard operator provides.  For degrees
`n ≥ 4` the standard integral of a flat family `F` converges absolutely on the half plane
`-n/2 < Re s`, which contains the cohomological point `s₀ = -3/2`, and is analytic there
(`CompactScalarConvergence.standard_integrable`, `standard_analyticAt`).  `IsStandardConvergent`
keeps exactly this information: `J` is meromorphic (indeed analytic) on that half plane and equals
the standard integral on a right half plane.  `RealizesStandardConv` and `RelatedConv` are
`RealizesStandard` and `StandardRelation.Related` with this predicate.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein

/-- `f` is meromorphic at every point of the half plane `c < Re s`. -/
def MeromorphicAboveRe (c : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, c < s.re → MeromorphicAt f s

/-- A standard family `J` for the flat family `F` in degree `d`: meromorphic on the half plane
`-d/2 < Re s` of absolute convergence, equal to the standard integral on a right half plane. -/
def IsStandardConvergent (d : ℕ) (F J : ℂ → AdelicGL → ℂ) : Prop :=
  (∀ g : AdelicGL, MeromorphicAboveRe (-(d : ℝ) / 2) (fun z => J z g)) ∧
  ∃ R : ℝ, ∀ s : ℂ, R < s.re → ∀ g : AdelicGL,
    MeasureTheory.Integrable (standardIntegrand F s g) radicalMeasure ∧
    J s g = ∫ u, standardIntegrand F s g u ∂radicalMeasure

/-- `RealizesStandard` with the half-plane continuation `IsStandardConvergent`. -/
def RealizesStandardConv {n : ℕ} (D : InducingData n)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) : Prop :=
  ∀ c, IsSourceCocycle D .plane c → ∀ z, Evaluates D .plane c z →
    ∀ h : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z ∈ boundarySummand D .plane,
    ∃ (F J : ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n),
      (∀ x m, IsFlatSection D (fun s g => (F s x g).val.coeff m)) ∧
      F cohomologicalPoint = c ∧
      (∀ x m, IsStandardConvergent n
        (fun s g => (F s x g).val.coeff m)
        (fun s g => (J s x g).val.coeff m)) ∧
      (∀ x g m, AnalyticAt ℂ
        (fun s => (J s x g).val.coeff m) cohomologicalPoint) ∧
      IsSourceCocycle D .line (J cohomologicalPoint) ∧
      ∃ z', Evaluates D .line (J cohomologicalPoint) z' ∧
        (T ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z,h⟩).val = classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z'

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

def RelatedConv {degree : ℕ} (data : InducingData degree)
    (plane : SourceSpace.sourceCocycles data .plane)
    (line : SourceSpace.sourceCocycles data .line) : Prop :=
  ∃ extension continuation :
      ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree,
    (∀ vertices monomial, IsFlatSection data (fun parameter argument =>
      (extension parameter vertices argument).val.coeff monomial)) ∧
    extension cohomologicalPoint = plane.val ∧
    (∀ vertices monomial, IsStandardConvergent degree
      (fun parameter argument =>
        (extension parameter vertices argument).val.coeff monomial)
      (fun parameter argument =>
        (continuation parameter vertices argument).val.coeff monomial)) ∧
    (∀ vertices argument monomial, AnalyticAt ℂ (fun parameter =>
      (continuation parameter vertices argument).val.coeff monomial)
      cohomologicalPoint) ∧
    continuation cohomologicalPoint = line.val

theorem realizesStandardConv_iff {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) :
    RealizesStandardConv data standard ↔
      ∀ plane : SourceSpace.sourceCocycles data .plane, ∃ line,
        RelatedConv data plane line ∧
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

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein
