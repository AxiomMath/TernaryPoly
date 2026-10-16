module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Stages
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open scoped NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticRealization

noncomputable def stageRealization (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    analyticStage data level radius positiveRadius →ₗ[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedRealization data level).comp
    (stageSmoothMap data level openness compactness radius positiveRadius)

theorem stageRealization_apply (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (element : analyticStage data level radius positiveRadius) (matrix : BinaryAdelicGL) :
    stageRealization data level openness compactness radius positiveRadius element matrix =
      data.realize (stageSmoothMap data level openness compactness radius positiveRadius element).val matrix := rfl

theorem stageRealization_continuous_iff_closed_graph (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL)) (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    Continuous (stageRealization data level openness compactness radius positiveRadius) ↔
      IsClosed ((stageRealization data level openness compactness radius positiveRadius).graph :
        Set (analyticStage data level radius positiveRadius × lp (fun _ : BinaryAdelicGL => ℂ) ⊤)) := by
  constructor
  · intro continuity
    exact isClosed_eq continuous_snd (continuity.comp continuous_fst)
  · exact (stageRealization data level openness compactness radius positiveRadius).continuous_of_isClosed_graph

/-- Point evaluations suffice here because the source stage and the sup-norm target are Banach spaces. -/
theorem stageRealization_continuous_iff_evaluations (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL)) (radius : ℝ≥0) (positiveRadius : 0 < radius) :
    Continuous (stageRealization data level openness compactness radius positiveRadius) ↔
      ∀ matrix : BinaryAdelicGL, Continuous
        (fun element : analyticStage data level radius positiveRadius =>
          data.realize (stageSmoothMap data level openness compactness radius positiveRadius element).val matrix) := by
  constructor
  · intro continuity matrix
    exact (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ matrix).continuous.comp continuity
  · intro evaluations
    apply (stageRealization_continuous_iff_closed_graph data level openness compactness radius positiveRadius).mpr
    have graphEquality :
        ((stageRealization data level openness compactness radius positiveRadius).graph :
          Set (analyticStage data level radius positiveRadius × lp (fun _ : BinaryAdelicGL => ℂ) ⊤)) =
        ⋂ matrix : BinaryAdelicGL, {pair | pair.2 matrix =
          data.realize (stageSmoothMap data level openness compactness radius positiveRadius pair.1).val matrix} := by
      ext pair
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro equality matrix
        exact congrArg (fun function : lp (fun _ : BinaryAdelicGL => ℂ) ⊤ => function matrix) equality
      · intro equality
        apply Subtype.ext
        exact funext equality
    rw [graphEquality]
    apply isClosed_iInter
    intro matrix
    exact isClosed_eq ((lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ matrix).continuous.comp continuous_snd)
      ((evaluations matrix).comp continuous_fst)

theorem stageRealization_bound_of_continuous (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL)) (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (continuity : Continuous (stageRealization data level openness compactness radius positiveRadius)) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ element : analyticStage data level radius positiveRadius,
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm
        (stageSmoothMap data level openness compactness radius positiveRadius element).val ≤ constant * ‖element‖ := by
  let realization : analyticStage data level radius positiveRadius →L[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
    ⟨stageRealization data level openness compactness radius positiveRadius, continuity⟩
  exact ⟨‖realization‖, realization.opNorm_nonneg, fun element => realization.le_opNorm element⟩

theorem stageRealization_bound_on_compact {Parameter : Type} [TopologicalSpace Parameter]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (continuity : Continuous (stageRealization data level openness compactness radius positiveRadius))
    (family : Parameter → analyticStage data level radius positiveRadius)
    {compactSet : Set Parameter} (compactParameter : IsCompact compactSet)
    (familyContinuous : ContinuousOn family compactSet) :
    ∃ bound : ℝ, ∀ parameter ∈ compactSet,
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm
        (stageSmoothMap data level openness compactness radius positiveRadius (family parameter)).val ≤ bound :=
  compactParameter.exists_bound_of_continuousOn (continuity.comp_continuousOn familyContinuous)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticRealization
