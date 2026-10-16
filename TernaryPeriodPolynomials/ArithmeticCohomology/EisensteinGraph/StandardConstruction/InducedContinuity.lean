module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FiniteLevelTopology
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Continuity

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Topology MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.InducedContinuity

theorem realGroup_continuous : Continuous realGroup :=
  TopologicalMatrices.generalLinearMap_continuous (RingHom.fst ℝ FiniteAdeles) continuous_fst

theorem finiteGroup_continuous : Continuous finiteGroup :=
  TopologicalMatrices.generalLinearMap_continuous (RingHom.snd ℝ FiniteAdeles) continuous_snd

theorem realGroup_atInfinity (real : RealGL3) : realGroup (atInfinity real) = real := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem finiteGroup_atInfinity (real : RealGL3) : finiteGroup (atInfinity real) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem realGroup_atFinite (finite : FiniteGL) : realGroup (atFinite finite) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem finiteGroup_atFinite (finite : FiniteGL) : finiteGroup (atFinite finite) = finite := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem adelic_ext {first second : AdelicGL} (real : realGroup first = realGroup second)
    (finite : finiteGroup first = finiteGroup second) : first = second := by
  apply GeneralLinearGroup.ext
  intro row column
  exact Prod.ext (congrArg (fun matrix => matrix.val row column) real)
    (congrArg (fun matrix => matrix.val row column) finite)

theorem split_right (element : AdelicGL) (reference : FiniteGL) :
    element = atFinite reference * atInfinity (realGroup element) *
      atFinite (reference⁻¹ * finiteGroup element) := by
  apply adelic_ext
  · simp only [map_mul, realGroup_atFinite, realGroup_atInfinity, one_mul, mul_one]
  · simp only [map_mul, finiteGroup_atFinite, finiteGroup_atInfinity, mul_one,
      mul_inv_cancel_left]

theorem induced_continuous {degree : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) : Continuous function := by
  apply continuous_iff_continuousAt.mpr
  intro element
  have localContinuous : Continuous (fun argument : AdelicGL =>
      function (atFinite (finiteGroup element) * atInfinity (realGroup argument))) :=
    (SmoothContinuity.induced_real_continuous data side parameter function induced
      (atFinite (finiteGroup element))).comp realGroup_continuous
  have near : ∀ᶠ argument : AdelicGL in 𝓝 element,
      (finiteGroup element)⁻¹ * finiteGroup argument ∈ finiteLevel := by
    exact (FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul finiteGroup_continuous)).mem_nhds (by simp)
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  filter_upwards [near] with argument membership
  calc
    function argument = function (atFinite (finiteGroup element) *
        atInfinity (realGroup argument) *
          atFinite ((finiteGroup element)⁻¹ * finiteGroup argument)) :=
      congrArg function (split_right argument (finiteGroup element))
    _ = _ := induced.2.1 ⟨_, membership⟩ _

theorem lineUnipotent_continuous :
    Continuous (fun coordinates : Adeles × Adeles => lineUnipotent coordinates.1 coordinates.2) := by
  apply Units.continuous_iff.mpr
  constructor
  all_goals
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp [upperUnipotent] <;> constructor <;> fun_prop

theorem standardIntegrand_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter)) (argument : AdelicGL) :
    Continuous (standardIntegrand extension parameter argument) := by
  exact (induced_continuous data .plane parameter (extension parameter) induced).comp
    ((continuous_const.mul lineUnipotent_continuous).mul continuous_const)

theorem standardIntegrand_aestronglyMeasurable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter)) (argument : AdelicGL) :
    AEStronglyMeasurable (standardIntegrand extension parameter argument) radicalMeasure :=
  (standardIntegrand_continuous data extension parameter induced argument).aestronglyMeasurable

def additiveCompact : Set Adeles := Set.Icc 0 1 ×ˢ Set.range integralEmbedding

theorem additiveCompact_isCompact : IsCompact additiveCompact :=
  isCompact_Icc.prod integralLattice_isCompact

theorem additiveDomain_subset_compact : additiveDomain ⊆ additiveCompact :=
  Set.prod_mono Set.Ico_subset_Icc_self Set.Subset.rfl

theorem continuous_integrableOn_radicalDomain (function : Adeles × Adeles → ℂ)
    (continuous : Continuous function) :
    IntegrableOn function (additiveDomain ×ˢ additiveDomain) radicalMeasure := by
  have integral : IntegrableOn function (additiveCompact ×ˢ additiveCompact) radicalMeasure :=
    ContinuousOn.integrableOn_compact
      (additiveCompact_isCompact.prod additiveCompact_isCompact) continuous.continuousOn
  exact integral.mono_set (Set.prod_mono additiveDomain_subset_compact additiveDomain_subset_compact)

theorem eisensteinSummand_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter)) (argument : AdelicGL)
    (flag : Flags .plane) :
    Continuous (fun coordinates : Adeles × Adeles => eisensteinSummand extension parameter
      (lineUnipotent coordinates.1 coordinates.2 * argument) flag) := by
  exact (induced_continuous data .plane parameter (extension parameter) induced).comp
    (continuous_const.mul (lineUnipotent_continuous.mul continuous_const))

theorem eisensteinSummand_integrableOn {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter)) (argument : AdelicGL)
    (flag : Flags .plane) :
    IntegrableOn (fun coordinates : Adeles × Adeles => eisensteinSummand extension parameter
      (lineUnipotent coordinates.1 coordinates.2 * argument) flag)
      (additiveDomain ×ˢ additiveDomain) radicalMeasure :=
  continuous_integrableOn_radicalDomain _
    (eisensteinSummand_continuous data extension parameter induced argument flag)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.InducedContinuity
