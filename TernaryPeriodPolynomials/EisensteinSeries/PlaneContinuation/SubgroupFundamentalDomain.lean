module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FundamentalIntegration

@[expose] public section


open MeasureTheory
open scoped Pointwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SubgroupFundamentalDomain

variable {ActingGroup Space : Type*} [Group ActingGroup] [MulAction ActingGroup Space]

def domain (subgroup : Subgroup ActingGroup) (original : Set Space) : Set Space :=
  ⋃ coset : ActingGroup ⧸ subgroup, coset.out⁻¹ • original

instance coset_countable [Countable ActingGroup] (subgroup : Subgroup ActingGroup) : Countable (ActingGroup ⧸ subgroup) :=
  Function.Injective.countable (f := Quotient.out) Quotient.out_injective

theorem mem_domain (subgroup : Subgroup ActingGroup) (original : Set Space) (point : Space) :
    point ∈ domain subgroup original ↔ ∃ coset : ActingGroup ⧸ subgroup, coset.out • point ∈ original := by
  simp only [domain, Set.mem_iUnion, Set.mem_smul_set_iff_inv_smul_mem, inv_inv]

theorem measurable [MeasurableSpace Space] [Countable ActingGroup] [MeasurableConstSMul ActingGroup Space]
    (subgroup : Subgroup ActingGroup) (original : Set Space) (originalMeasurable : MeasurableSet original) :
    MeasurableSet (domain subgroup original) :=
  MeasurableSet.iUnion (fun coset => originalMeasurable.const_smul coset.out⁻¹)

theorem unique (subgroup : Subgroup ActingGroup) (original : Set Space)
    (originalUnique : ∀ point, ∃! element : ActingGroup, element • point ∈ original) (point : Space) :
    ∃! element : subgroup, element • point ∈ domain subgroup original := by
  obtain ⟨element, membership, uniqueness⟩ := originalUnique point
  obtain ⟨correction, representative⟩ := QuotientGroup.mk_out_eq_mul subgroup element
  have existsRepresentative : correction⁻¹ • point ∈ domain subgroup original := by
    apply (mem_domain subgroup original _).mpr
    refine ⟨QuotientGroup.mk element, ?_⟩
    rw [representative]
    change (element * correction.val) • (correction.val⁻¹ • point) ∈ original
    simpa only [mul_smul, smul_inv_smul] using membership
  refine ⟨correction⁻¹, existsRepresentative, ?_⟩
  intro other otherMembership
  obtain ⟨firstCoset, firstMem⟩ := (mem_domain subgroup original _).mp otherMembership
  obtain ⟨secondCoset, secondMem⟩ := (mem_domain subgroup original _).mp existsRepresentative
  change firstCoset.out • (other.val • point) ∈ original at firstMem
  change secondCoset.out • ((correction⁻¹).val • point) ∈ original at secondMem
  rw [← mul_smul] at firstMem secondMem
  have firstEquation : firstCoset.out * other.val = element := uniqueness _ firstMem
  have secondEquation : secondCoset.out * (correction⁻¹).val = element := uniqueness _ secondMem
  have cosetEquation : firstCoset = secondCoset := by
    have equation := congrArg (QuotientGroup.mk (s := subgroup)) (firstEquation.trans secondEquation.symm)
    simpa only [QuotientGroup.mk_mul_of_mem _ other.property,
      QuotientGroup.mk_mul_of_mem _ (correction⁻¹).property, QuotientGroup.out_eq'] using equation
  rw [cosetEquation] at firstEquation
  apply Subtype.ext
  exact mul_left_cancel (firstEquation.trans secondEquation.symm)

theorem fundamental [MeasurableSpace Space] [Countable ActingGroup] [MeasurableConstSMul ActingGroup Space]
    (subgroup : Subgroup ActingGroup) (original : Set Space) (originalMeasurable : MeasurableSet original)
    (originalUnique : ∀ point, ∃! element : ActingGroup, element • point ∈ original) (measure : Measure Space) :
    IsFundamentalDomain subgroup (domain subgroup original) measure :=
  IsFundamentalDomain.mk' (measurable subgroup original originalMeasurable).nullMeasurableSet
    (unique subgroup original originalUnique)

theorem pieces_disjoint (subgroup : Subgroup ActingGroup) (original : Set Space)
    (originalUnique : ∀ point, ∃! element : ActingGroup, element • point ∈ original) :
    Pairwise (fun first second : ActingGroup ⧸ subgroup => Disjoint (first.out⁻¹ • original) (second.out⁻¹ • original)) := by
  intro first second different
  apply Set.disjoint_left.mpr
  intro point firstMem secondMem
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv] at firstMem secondMem
  obtain ⟨element, _, uniqueness⟩ := originalUnique point
  have equality : first.out = second.out := (uniqueness _ firstMem).trans (uniqueness _ secondMem).symm
  apply different
  simpa only [QuotientGroup.out_eq'] using congrArg (QuotientGroup.mk (s := subgroup)) equality

theorem hasSum_integral [MeasurableSpace Space] [Countable ActingGroup] [MeasurableConstSMul ActingGroup Space]
    (subgroup : Subgroup ActingGroup) (original : Set Space) (originalMeasurable : MeasurableSet original)
    (originalUnique : ∀ point, ∃! element : ActingGroup, element • point ∈ original)
    (measure : Measure Space) [SMulInvariantMeasure ActingGroup Space measure]
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (function : Space → Target) (integrable : IntegrableOn function (domain subgroup original) measure) :
    HasSum (fun coset : ActingGroup ⧸ subgroup => ∫ point in original, function (coset.out⁻¹ • point) ∂measure)
      (∫ point in domain subgroup original, function point ∂measure) := by
  have result := hasSum_integral_iUnion (fun coset : ActingGroup ⧸ subgroup => originalMeasurable.const_smul coset.out⁻¹)
    (pieces_disjoint subgroup original originalUnique) integrable
  simpa only [FundamentalIntegration.integral_translate, domain] using result

theorem norm_integral_summable [MeasurableSpace Space] [Countable ActingGroup] [MeasurableConstSMul ActingGroup Space]
    (subgroup : Subgroup ActingGroup) (original : Set Space) (originalMeasurable : MeasurableSet original)
    (originalUnique : ∀ point, ∃! element : ActingGroup, element • point ∈ original)
    (measure : Measure Space) [SMulInvariantMeasure ActingGroup Space measure]
    {Target : Type*} [NormedAddCommGroup Target]
    (function : Space → Target) (integrable : IntegrableOn function (domain subgroup original) measure) :
    Summable (fun coset : ActingGroup ⧸ subgroup => ∫ point in original, ‖function (coset.out⁻¹ • point)‖ ∂measure) :=
  (hasSum_integral subgroup original originalMeasurable originalUnique measure _ integrable.norm).summable

theorem lintegral_translate [MeasurableSpace Space] [MeasurableConstSMul ActingGroup Space]
    (measure : Measure Space) [SMulInvariantMeasure ActingGroup Space measure]
    (function : Space → ENNReal) (original : Set Space) (element : ActingGroup) :
    ∫⁻ point in element • original, function point ∂measure =
      ∫⁻ point in original, function (element • point) ∂measure :=
  ((measurePreserving_smul element measure).setLIntegral_comp_emb
    (MeasurableEquiv.smul element).measurableEmbedding function original).symm

theorem integrable_of_periodized_bound [MeasurableSpace Space] [Countable ActingGroup] [MeasurableConstSMul ActingGroup Space]
    (subgroup : Subgroup ActingGroup) (original : Set Space)
    (measure : Measure Space) [SMulInvariantMeasure ActingGroup Space measure]
    (function : Space → ℂ) (functionMeasurable : Measurable function)
    (bound : Space → ℝ) (boundIntegrable : IntegrableOn bound original measure)
    (summable : ∀ point, Summable (fun coset : ActingGroup ⧸ subgroup => ‖function (coset.out⁻¹ • point)‖))
    (bounded : ∀ point, (∑' coset : ActingGroup ⧸ subgroup, ‖function (coset.out⁻¹ • point)‖) ≤ bound point) :
    IntegrableOn function (domain subgroup original) measure := by
  refine ⟨functionMeasurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    _ ≤ ∑' coset : ActingGroup ⧸ subgroup, ∫⁻ point in coset.out⁻¹ • original, ENNReal.ofReal ‖function point‖ ∂measure :=
      lintegral_iUnion_le _ _
    _ = ∑' coset : ActingGroup ⧸ subgroup, ∫⁻ point in original, ENNReal.ofReal ‖function (coset.out⁻¹ • point)‖ ∂measure := by
      apply tsum_congr
      intro coset
      exact lintegral_translate measure _ original coset.out⁻¹
    _ = ∫⁻ point in original, ∑' coset : ActingGroup ⧸ subgroup, ENNReal.ofReal ‖function (coset.out⁻¹ • point)‖ ∂measure :=
      (lintegral_tsum (μ := measure.restrict original) (fun coset : ActingGroup ⧸ subgroup =>
        (functionMeasurable.norm.ennreal_ofReal.comp (measurable_const_smul coset.out⁻¹)).aemeasurable)).symm
    _ ≤ ∫⁻ point in original, ENNReal.ofReal (bound point) ∂measure := by
      apply lintegral_mono
      intro point
      exact (le_of_eq (ENNReal.ofReal_tsum_of_nonneg
        (fun coset : ActingGroup ⧸ subgroup => norm_nonneg (function (coset.out⁻¹ • point))) (summable point)).symm).trans
          (ENNReal.ofReal_le_ofReal (bounded point))
    _ < ⊤ := boundIntegrable.lintegral_lt_top

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SubgroupFundamentalDomain
