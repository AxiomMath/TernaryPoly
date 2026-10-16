module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ChartIntegrals
public import Mathlib.Tactic.FunProp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem planeUnipotent_continuous : Continuous (fun coordinates : Adeles × Adeles =>
    planeUnipotent coordinates.1 coordinates.2) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column
  all_goals fin_cases row <;> fin_cases column
  all_goals first | exact continuous_const | exact continuous_fst | exact continuous_snd |
    exact continuous_fst.neg | exact continuous_snd.neg

theorem lineUnipotent_continuous : Continuous (fun coordinates : Adeles × Adeles =>
    lineUnipotent coordinates.1 coordinates.2) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column
  all_goals fin_cases row <;> fin_cases column
  all_goals first | exact continuous_const | exact continuous_fst | exact continuous_snd |
    exact continuous_fst.neg | exact continuous_snd.neg

theorem lowerPlaneUnipotent_continuous : Continuous (fun coordinates : Adeles × Adeles =>
    lowerPlaneUnipotent coordinates.1 coordinates.2) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column
  all_goals fin_cases row <;> fin_cases column
  all_goals first | exact continuous_const | exact continuous_fst | exact continuous_snd |
    exact continuous_fst.neg | exact continuous_snd.neg

theorem planeBinaryUnipotent_continuous : Continuous (fun coordinate : Adeles =>
    planeLevi (binaryUnipotent coordinate) 1) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column
  all_goals fin_cases row <;> fin_cases column
  all_goals first | exact continuous_const | exact continuous_id | exact continuous_id.neg

theorem continuous_radicalDomain_integrable {E : Type*} [NormedAddCommGroup E]
    {function : Adeles × Adeles → E} (continuous : Continuous function) :
    Integrable function planeDomainMeasure := by
  let container : Set Adeles := Set.Icc 0 1 ×ˢ Set.range integralEmbedding
  have compact : IsCompact container := isCompact_Icc.prod integralLattice_isCompact
  have subset : additiveDomain ⊆ container := by
    intro coordinates in_domain
    exact ⟨⟨in_domain.1.1, le_of_lt in_domain.1.2⟩, in_domain.2⟩
  rw [planeDomainMeasure_eq]
  exact (ContinuousOn.integrableOn_compact (compact.prod compact) continuous.continuousOn).mono_set
    (Set.prod_mono subset subset)

theorem eisensteinSummand_continuous
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter)) (flag : Flags .plane) :
    Continuous (fun groupElement => eisensteinSummand family parameter groupElement flag) :=
  (induced_continuous induced).comp (continuous_const.mul continuous_id)

theorem plane_summand_integrable
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL) (flag : Flags .plane) :
    Integrable (fun coordinates : Adeles × Adeles =>
      eisensteinSummand family parameter (planeUnipotent coordinates.1 coordinates.2 * groupElement) flag)
        planeDomainMeasure :=
  continuous_radicalDomain_integrable
    ((eisensteinSummand_continuous induced flag).comp (planeUnipotent_continuous.mul continuous_const))

theorem line_summand_integrable
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL) (flag : Flags .plane) :
    Integrable (fun coordinates : Adeles × Adeles =>
      eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement) flag)
        planeDomainMeasure :=
  continuous_radicalDomain_integrable
    ((eisensteinSummand_continuous induced flag).comp (lineUnipotent_continuous.mul continuous_const))

theorem finiteOpenOrbitKernel_continuous
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionValue : AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (slope : ℚ) (groupElement : AdelicGL) :
    Continuous (finiteOpenOrbitKernel sectionValue slope groupElement) :=
  (induced_continuous induced).comp
    ((planeBinaryUnipotent_continuous.comp continuous_fst).mul
      ((lowerPlaneUnipotent_continuous.comp (continuous_const.prodMk continuous_snd)).mul continuous_const))

theorem infiniteOpenOrbitKernel_continuous
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionValue : AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (groupElement : AdelicGL) : Continuous (infiniteOpenOrbitKernel sectionValue groupElement) :=
  (induced_continuous induced).comp
    ((planeBinaryUnipotent_continuous.comp continuous_fst).mul
      ((lowerPlaneUnipotent_continuous.comp (continuous_const.prodMk continuous_snd)).mul continuous_const))

theorem standardIntegrand_continuous
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter)) (groupElement : AdelicGL) :
    Continuous (standardIntegrand family parameter groupElement) :=
  (induced_continuous induced).comp ((continuous_const.mul lineUnipotent_continuous).mul continuous_const)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
