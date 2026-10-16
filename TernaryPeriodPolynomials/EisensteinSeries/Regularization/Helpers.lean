module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem regularization_of_nonnegative_order
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (nonnegative_order : ∀ groupElement,
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter groupElement)
        cohomologicalPoint) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation sectionFamily repaired ∧
        SameOffCohomologicalPoint continuation repaired ∧
        ∀ groupElement,
          AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
            cohomologicalPoint := by
  let repaired : ℂ → AdelicGL → ℂ := fun parameter groupElement =>
    toMeromorphicNFAt (fun nearbyParameter => continuation nearbyParameter groupElement)
      cohomologicalPoint parameter
  have same_off : SameOffCohomologicalPoint continuation repaired := by
    intro parameter parameter_ne groupElement
    exact ((continuation_spec.1 groupElement cohomologicalPoint).eqOn_compl_singleton_toMeromorphicNFAt
      parameter_ne).symm
  have repaired_analytic : ∀ groupElement,
      AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
        cohomologicalPoint := by
    intro groupElement
    exact ((continuation_spec.1 groupElement cohomologicalPoint).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp
        (nonnegative_order groupElement)
  refine ⟨repaired, ⟨?_, ?_⟩, same_off, repaired_analytic⟩
  · intro groupElement parameter
    by_cases at_point : parameter = cohomologicalPoint
    · subst parameter
      exact (repaired_analytic groupElement).meromorphicAt
    · apply (continuation_spec.1 groupElement parameter).congr
      filter_upwards [eventually_ne_nhdsWithin at_point] with nearbyParameter nearby_ne
      exact (same_off nearbyParameter nearby_ne groupElement).symm
  · obtain ⟨threshold, convergence⟩ := continuation_spec.2
    refine ⟨max threshold cohomologicalPoint.re, ?_⟩
    intro parameter parameter_large groupElement
    have parameter_ne : parameter ≠ cohomologicalPoint := by
      intro at_point
      have point_lt : cohomologicalPoint.re < parameter.re :=
        lt_of_le_of_lt (le_max_right _ _) parameter_large
      exact (lt_irrefl _) (at_point ▸ point_lt)
    rw [same_off parameter parameter_ne groupElement]
    exact convergence parameter
      (lt_of_le_of_lt (le_max_left _ _) parameter_large) groupElement

theorem nonnegative_order_of_regularization
    {continuation repaired : ℂ → AdelicGL → ℂ}
    (same_off : SameOffCohomologicalPoint continuation repaired)
    (repaired_analytic : ∀ groupElement,
      AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
        cohomologicalPoint) :
    ∀ groupElement,
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter groupElement)
        cohomologicalPoint := by
  intro groupElement
  have same_germ :
      (fun parameter => continuation parameter groupElement) =ᶠ[
        nhdsWithin cohomologicalPoint {cohomologicalPoint}ᶜ]
        (fun parameter => repaired parameter groupElement) := by
    filter_upwards [self_mem_nhdsWithin] with parameter parameter_ne
    exact (same_off parameter parameter_ne groupElement).symm
  rw [meromorphicOrderAt_congr same_germ]
  exact (repaired_analytic groupElement).meromorphicOrderAt_nonneg

theorem regularization_iff_nonnegative_order
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation) :
    (∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation sectionFamily repaired ∧
        SameOffCohomologicalPoint continuation repaired ∧
        ∀ groupElement,
          AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
            cohomologicalPoint) ↔
    ∀ groupElement,
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter groupElement)
        cohomologicalPoint := by
  constructor
  · rintro ⟨repaired, _, same_off, repaired_analytic⟩
    exact nonnegative_order_of_regularization same_off repaired_analytic
  · exact regularization_of_nonnegative_order continuation_spec

theorem parameter_strictly_negative
    {degree : ℕ} (degree_positive : 0 < degree) :
    (3 : ℝ) / 2 - ((degree : ℝ) + 3) / 2 < 0 := by
  have degree_real_positive : 0 < (degree : ℝ) := by
    exact_mod_cast degree_positive
  have parameter_eq : (3 : ℝ) / 2 - ((degree : ℝ) + 3) / 2 = -(degree : ℝ) / 2 := by
    ring
  rw [parameter_eq]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos degree_real_positive) (by norm_num)

theorem normPower_ne_zero (idele : Adelesˣ) (parameter : ℂ) :
    normPower idele parameter ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem normPower_add (idele : Adelesˣ) (firstParameter secondParameter : ℂ) :
    normPower idele (firstParameter + secondParameter) =
      normPower idele firstParameter * normPower idele secondParameter := by
  simp only [normPower, add_mul, Complex.exp_add]

theorem normPower_norm (idele : Adelesˣ) (parameter : ℂ) :
    ‖normPower idele parameter‖ =
      Real.exp (parameter.re * Real.log (adeleNorm idele : ℝ)) := by
  simp only [normPower, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem normPower_zero (idele : Adelesˣ) : normPower idele 0 = 1 := by
  simp only [normPower, zero_mul, Complex.exp_zero]

theorem induced_binary_orbit_bounded
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (groupElement : AdelicGL) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ binaryMatrix : BinaryAdelicGL,
      ‖normPower (Matrix.GeneralLinearGroup.det binaryMatrix)
          (-binaryInductionExponent degree .plane parameter) *
        sectionValue (planeLevi binaryMatrix 1 * groupElement)‖ ≤ bound := by
  obtain ⟨vector, realized⟩ := induced.2.2.2.2.2 groupElement
  obtain ⟨bound, vector_bounded⟩ := inducingData.cusp.bounded vector
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro binaryMatrix
  have value_eq := congrFun realized binaryMatrix
  exact (value_eq ▸ vector_bounded binaryMatrix).trans (le_max_right _ _)

theorem flat_section_compact_levi_norm_bound
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData sectionFamily)
    (compactElement : AdelicGL)
    (compact_spec : inMaximalCompact compactElement) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ binaryMatrix : BinaryAdelicGL,
      ‖sectionFamily parameter (planeLevi binaryMatrix 1 * compactElement)‖ ≤
        Real.exp ((binaryInductionExponent degree .plane parameter).re *
          Real.log (adeleNorm (Matrix.GeneralLinearGroup.det binaryMatrix) : ℝ)) *
          bound := by
  obtain ⟨bound, bound_nonnegative, orbit_bounded⟩ :=
    induced_binary_orbit_bounded (flat_family.1 cohomologicalPoint) compactElement
  refine ⟨bound, bound_nonnegative, ?_⟩
  intro parameter binaryMatrix
  have normalized_bound :
      ‖normPower (Matrix.GeneralLinearGroup.det binaryMatrix)
          (-binaryInductionExponent degree .plane parameter) *
        sectionFamily parameter (planeLevi binaryMatrix 1 * compactElement)‖ ≤
          bound := by
    rw [flat_family.2.2 parameter binaryMatrix compactElement compact_spec]
    exact orbit_bounded binaryMatrix
  have product_identity :
      normPower (Matrix.GeneralLinearGroup.det binaryMatrix)
        (binaryInductionExponent degree .plane parameter) *
      normPower (Matrix.GeneralLinearGroup.det binaryMatrix)
        (-binaryInductionExponent degree .plane parameter) = 1 := by
    rw [← normPower_add, add_neg_cancel, normPower_zero]
  have value_identity :
      sectionFamily parameter (planeLevi binaryMatrix 1 * compactElement) =
      normPower (Matrix.GeneralLinearGroup.det binaryMatrix)
        (binaryInductionExponent degree .plane parameter) *
        (normPower (Matrix.GeneralLinearGroup.det binaryMatrix)
          (-binaryInductionExponent degree .plane parameter) *
          sectionFamily parameter (planeLevi binaryMatrix 1 * compactElement)) := by
    rw [← mul_assoc, product_identity, one_mul]
  rw [value_identity, norm_mul, normPower_norm]
  exact mul_le_mul_of_nonneg_left normalized_bound (Real.exp_nonneg _)

theorem flat_section_compact_levi_scaling
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData sectionFamily)
    (parameter : ℂ) (binaryMatrix : BinaryAdelicGL) (compactElement : AdelicGL)
    (compact_spec : inMaximalCompact compactElement) :
    sectionFamily parameter (planeLevi binaryMatrix 1 * compactElement) =
      normPower (Matrix.GeneralLinearGroup.det binaryMatrix)
        (inductionExponent .plane parameter) *
      sectionFamily cohomologicalPoint (planeLevi binaryMatrix 1 * compactElement) := by
  have exponent_at_point : inductionExponent .plane cohomologicalPoint = 0 := by
    norm_num [inductionExponent, cohomologicalPoint]
  have exponent_identity :
      -binaryInductionExponent degree .plane parameter + inductionExponent .plane parameter =
        -binaryInductionExponent degree .plane cohomologicalPoint := by
    simp only [binaryInductionExponent, exponent_at_point, add_zero]
    ring
  apply mul_left_cancel₀
    (normPower_ne_zero (Matrix.GeneralLinearGroup.det binaryMatrix)
      (-binaryInductionExponent degree .plane parameter))
  rw [← mul_assoc, ← normPower_add, exponent_identity]
  exact flat_family.2.2 parameter binaryMatrix compactElement compact_spec

theorem continuation_germs_agree
    {sectionFamily firstContinuation secondContinuation : ℂ → AdelicGL → ℂ}
    (first_spec : IsEisensteinContinuation sectionFamily firstContinuation)
    (second_spec : IsEisensteinContinuation sectionFamily secondContinuation)
    (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearbyParameter => firstContinuation nearbyParameter groupElement) =ᶠ[
      nhdsWithin parameter {parameter}ᶜ]
      (fun nearbyParameter => secondContinuation nearbyParameter groupElement) := by
  obtain ⟨first_threshold, first_convergence⟩ := first_spec.2
  obtain ⟨second_threshold, second_convergence⟩ := second_spec.2
  let threshold : ℝ := max first_threshold second_threshold
  let base : ℂ := (threshold + 1 : ℝ)
  have base_large : threshold < base.re := by
    dsimp [base]
    exact lt_add_one threshold
  have same_near_base :
      (fun nearbyParameter => firstContinuation nearbyParameter groupElement) =ᶠ[
        nhds base]
        (fun nearbyParameter => secondContinuation nearbyParameter groupElement) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      base_large] with nearbyParameter nearby_large
    exact (first_convergence nearbyParameter
      (lt_of_le_of_lt (le_max_left _ _) nearby_large) groupElement).unique
        (second_convergence nearbyParameter
          (lt_of_le_of_lt (le_max_right _ _) nearby_large) groupElement)
  have difference_meromorphic : MeromorphicOn
      (fun nearbyParameter => firstContinuation nearbyParameter groupElement -
        secondContinuation nearbyParameter groupElement) Set.univ := by
    intro nearbyParameter _
    exact (first_spec.1 groupElement nearbyParameter).sub
      (second_spec.1 groupElement nearbyParameter)
  have zero_order_base : meromorphicOrderAt
      (fun nearbyParameter => firstContinuation nearbyParameter groupElement -
        secondContinuation nearbyParameter groupElement) base = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [same_near_base.filter_mono nhdsWithin_le_nhds] with
      nearbyParameter same_value
    exact sub_eq_zero.mpr same_value
  have zero_order_parameter : meromorphicOrderAt
      (fun nearbyParameter => firstContinuation nearbyParameter groupElement -
        secondContinuation nearbyParameter groupElement) parameter = ⊤ := by
    by_contra order_ne_top
    exact (difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ parameter) (Set.mem_univ base) order_ne_top)
        zero_order_base
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp zero_order_parameter] with
    nearbyParameter difference_zero
  exact sub_eq_zero.mp difference_zero

theorem nonnegative_order_of_local_analytic_sum
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (local_sum : ∀ groupElement, ∃ domain : Set ℂ,
      IsOpen domain ∧ IsPreconnected domain ∧ cohomologicalPoint ∈ domain ∧
      (∀ threshold : ℝ, ∃ parameter ∈ domain, threshold < parameter.re) ∧
      ∃ analyticSum : ℂ → ℂ,
        AnalyticOnNhd ℂ analyticSum domain ∧
        ∀ parameter ∈ domain,
          HasSum (eisensteinSummand sectionFamily parameter groupElement)
            (analyticSum parameter)) :
    ∀ groupElement,
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter groupElement)
        cohomologicalPoint := by
  intro groupElement
  obtain ⟨domain, domain_open, domain_connected, point_in_domain, domain_unbounded,
    analyticSum, sum_analytic, sum_spec⟩ := local_sum groupElement
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  obtain ⟨base, base_in_domain, base_large⟩ := domain_unbounded threshold
  have same_near_base :
      (fun parameter => continuation parameter groupElement) =ᶠ[nhds base]
        analyticSum := by
    filter_upwards [domain_open.mem_nhds base_in_domain,
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem base_large]
      with parameter parameter_in_domain parameter_large
    exact (convergence parameter parameter_large groupElement).unique
      (sum_spec parameter parameter_in_domain)
  have difference_meromorphic : MeromorphicOn
      (fun parameter => continuation parameter groupElement - analyticSum parameter)
      domain := by
    intro parameter parameter_in_domain
    exact (continuation_spec.1 groupElement parameter).sub
      (sum_analytic parameter parameter_in_domain).meromorphicAt
  have zero_order_base : meromorphicOrderAt
      (fun parameter => continuation parameter groupElement - analyticSum parameter)
      base = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [same_near_base.filter_mono nhdsWithin_le_nhds]
      with parameter same_value
    exact sub_eq_zero.mpr same_value
  have zero_order_point : meromorphicOrderAt
      (fun parameter => continuation parameter groupElement - analyticSum parameter)
      cohomologicalPoint = ⊤ := by
    by_contra order_ne_top
    exact (difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      domain_connected point_in_domain base_in_domain order_ne_top) zero_order_base
  have same_germ :
      (fun parameter => continuation parameter groupElement) =ᶠ[
        nhdsWithin cohomologicalPoint {cohomologicalPoint}ᶜ] analyticSum := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp zero_order_point]
      with parameter difference_zero
    exact sub_eq_zero.mp difference_zero
  rw [meromorphicOrderAt_congr same_germ]
  exact (sum_analytic cohomologicalPoint point_in_domain).meromorphicOrderAt_nonneg

theorem nonnegative_order_of_local_uniform_convergence
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData sectionFamily)
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (uniform_convergence : ∀ groupElement, ∃ domain : Set ℂ,
      IsOpen domain ∧ IsPreconnected domain ∧ cohomologicalPoint ∈ domain ∧
      (∀ threshold : ℝ, ∃ parameter ∈ domain, threshold < parameter.re) ∧
      SummableLocallyUniformlyOn
        (fun flag parameter => eisensteinSummand sectionFamily parameter groupElement flag)
        domain) :
    ∀ groupElement,
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter groupElement)
        cohomologicalPoint := by
  apply nonnegative_order_of_local_analytic_sum continuation_spec
  intro groupElement
  obtain ⟨domain, domain_open, domain_connected, point_in_domain,
    domain_unbounded, convergence⟩ := uniform_convergence groupElement
  refine ⟨domain, domain_open, domain_connected, point_in_domain, domain_unbounded,
    (fun parameter => ∑' flag, eisensteinSummand sectionFamily parameter groupElement flag),
    ?_, ?_⟩
  · apply DifferentiableOn.analyticOnNhd _ domain_open
    apply convergence.differentiableOn domain_open
    intro flag parameter _
    exact (flat_family.2.1 (rationalGroup flag.out⁻¹ * groupElement)
      parameter).differentiableAt
  · intro parameter parameter_in_domain
    exact (convergence.summable parameter_in_domain).hasSum

theorem regularization_of_analytic_continuation
    {sectionFamily continuation analyticContinuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (analytic_continuation_spec : IsEisensteinContinuation sectionFamily analyticContinuation)
    (analytic_continuation_at_point : ∀ groupElement,
      AnalyticAt ℂ (fun parameter => analyticContinuation parameter groupElement)
        cohomologicalPoint) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation sectionFamily repaired ∧
        SameOffCohomologicalPoint continuation repaired ∧
        ∀ groupElement,
          AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
            cohomologicalPoint := by
  apply regularization_of_nonnegative_order continuation_spec
  intro groupElement
  rw [meromorphicOrderAt_congr (continuation_germs_agree continuation_spec
    analytic_continuation_spec groupElement cohomologicalPoint)]
  exact (analytic_continuation_at_point groupElement).meromorphicOrderAt_nonneg

theorem regularization_of_plane_holomorphy
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (holomorphy : PlaneEisensteinHolomorphic inducingData)
    (flat_family : IsFlatSection inducingData sectionFamily)
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation sectionFamily repaired ∧
        SameOffCohomologicalPoint continuation repaired ∧
        ∀ groupElement,
          AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
            cohomologicalPoint := by
  obtain ⟨analyticContinuation, analytic_spec, analytic_at_point⟩ :=
    holomorphy.2 sectionFamily flat_family
  exact regularization_of_analytic_continuation continuation_spec
    analytic_spec analytic_at_point

theorem nonnegative_order_of_eventually_bounded
    {continuation : ℂ → AdelicGL → ℂ}
    (bounded_near_point : ∀ groupElement, ∃ bound : ℝ,
      ∀ᶠ parameter in nhdsWithin cohomologicalPoint {cohomologicalPoint}ᶜ,
        ‖continuation parameter groupElement‖ ≤ bound) :
    ∀ groupElement,
      0 ≤ meromorphicOrderAt (fun parameter => continuation parameter groupElement)
        cohomologicalPoint := by
  intro groupElement
  obtain ⟨bound, bounded⟩ := bounded_near_point groupElement
  by_contra order_negative
  have divergent := tendsto_cobounded_of_meromorphicOrderAt_neg
    (lt_of_not_ge order_negative)
  have large := divergent.eventually (eventually_cobounded_le_norm (bound + 1))
  have impossible : ∀ᶠ parameter in
      nhdsWithin cohomologicalPoint {cohomologicalPoint}ᶜ, False := by
    filter_upwards [bounded, large] with parameter parameter_bounded parameter_large
    exact (not_le_of_gt (lt_add_one bound))
      (parameter_large.trans parameter_bounded)
  exact (Filter.Eventually.exists impossible).choose_spec

theorem regularization_of_eventually_bounded
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (bounded_near_point : ∀ groupElement, ∃ bound : ℝ,
      ∀ᶠ parameter in nhdsWithin cohomologicalPoint {cohomologicalPoint}ᶜ,
        ‖continuation parameter groupElement‖ ≤ bound) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation sectionFamily repaired ∧
        SameOffCohomologicalPoint continuation repaired ∧
        ∀ groupElement,
          AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
            cohomologicalPoint := by
  exact regularization_of_nonnegative_order continuation_spec
    (nonnegative_order_of_eventually_bounded bounded_near_point)

theorem simple_pole_has_no_analytic_repair :
    ¬ ∃ repaired : ℂ → AdelicGL → ℂ,
      SameOffCohomologicalPoint (fun parameter _ => (parameter - cohomologicalPoint)⁻¹)
        repaired ∧
        ∀ groupElement,
          AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
            cohomologicalPoint := by
  rintro ⟨repaired, same_off, repaired_analytic⟩
  have order_nonnegative :=
    nonnegative_order_of_regularization same_off repaired_analytic (1 : AdelicGL)
  rw [fun_meromorphicOrderAt_inv, meromorphicOrderAt_id_sub_const] at order_nonnegative
  have negative_one_eq : -(1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) :=
    (WithTop.LinearOrderedAddCommGroup.coe_neg (1 : ℤ)).symm
  rw [negative_one_eq] at order_nonnegative
  have integer_nonnegative : (0 : ℤ) ≤ -1 := WithTop.coe_nonneg.mp order_nonnegative
  norm_num at integer_nonnegative

theorem analytic_repair_unique
    {continuation firstRepair secondRepair : ℂ → AdelicGL → ℂ}
    (first_same_off : SameOffCohomologicalPoint continuation firstRepair)
    (second_same_off : SameOffCohomologicalPoint continuation secondRepair)
    (first_analytic : ∀ groupElement,
      AnalyticAt ℂ (fun parameter => firstRepair parameter groupElement)
        cohomologicalPoint)
    (second_analytic : ∀ groupElement,
      AnalyticAt ℂ (fun parameter => secondRepair parameter groupElement)
        cohomologicalPoint) :
    firstRepair = secondRepair := by
  funext parameter groupElement
  by_cases at_point : parameter = cohomologicalPoint
  · subst parameter
    have same_germ :
        (fun nearbyParameter => firstRepair nearbyParameter groupElement) =ᶠ[
          nhdsWithin cohomologicalPoint {cohomologicalPoint}ᶜ]
          (fun nearbyParameter => secondRepair nearbyParameter groupElement) := by
      filter_upwards [self_mem_nhdsWithin] with nearbyParameter nearby_ne
      exact (first_same_off nearbyParameter nearby_ne groupElement).trans
        (second_same_off nearbyParameter nearby_ne groupElement).symm
    exact (((first_analytic groupElement).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (second_analytic groupElement).continuousAt).mp same_germ).eq_of_nhds
  · exact (first_same_off parameter at_point groupElement).trans
      (second_same_off parameter at_point groupElement).symm

theorem regularization_iff_nonnegative_order_paper :
    (∀ degree : ℕ, 0 < degree → ∀ inducingData : InducingData degree,
      inducingData.chi = trivialCharacter →
      ∀ sectionFamily : ℂ → AdelicGL → ℂ, IsFlatSection inducingData sectionFamily →
      ∀ continuation : ℂ → AdelicGL → ℂ,
        IsEisensteinContinuation sectionFamily continuation →
      ∃ repaired : ℂ → AdelicGL → ℂ,
        IsEisensteinContinuation sectionFamily repaired ∧
          SameOffCohomologicalPoint continuation repaired ∧
          ∀ groupElement,
            AnalyticAt ℂ (fun parameter => repaired parameter groupElement)
              cohomologicalPoint) ↔
    (∀ degree : ℕ, 0 < degree → ∀ inducingData : InducingData degree,
      inducingData.chi = trivialCharacter →
      ∀ sectionFamily : ℂ → AdelicGL → ℂ, IsFlatSection inducingData sectionFamily →
      ∀ continuation : ℂ → AdelicGL → ℂ,
        IsEisensteinContinuation sectionFamily continuation →
      ∀ groupElement,
        0 ≤ meromorphicOrderAt (fun parameter => continuation parameter groupElement)
          cohomologicalPoint) := by
  constructor
  · intro regularization degree degree_positive inducingData character_trivial
      sectionFamily flat_family continuation continuation_spec
    exact (regularization_iff_nonnegative_order continuation_spec).mp
      (regularization degree degree_positive inducingData character_trivial
        sectionFamily flat_family continuation continuation_spec)
  · intro nonnegative_order degree degree_positive inducingData character_trivial
      sectionFamily flat_family continuation continuation_spec
    exact regularization_of_nonnegative_order continuation_spec
      (nonnegative_order degree degree_positive inducingData character_trivial
        sectionFamily flat_family continuation continuation_spec)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
