module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SubgroupCosetDomain
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


open MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem subgroupCosetDomain_lintegral {G X : Type*} [Group G] [Countable G]
    [MulAction G X] [MeasurableSpace X] [MeasurableConstSMul G X]
    (subgroup : Subgroup G) {domain : Set X} {measure : Measure X}
    [SMulInvariantMeasure G X measure]
    (measurable : MeasurableSet domain) (fundamental : IsFundamentalDomain G domain measure)
    (function : X → ℝ≥0∞) :
    (∫⁻ point in subgroupCosetDomain subgroup domain, function point ∂measure) =
      ∑' coset : G ⧸ subgroup, ∫⁻ point in domain, function ((Quotient.out coset)⁻¹ • point) ∂measure := by
  rw [subgroupCosetDomain, lintegral_iUnion₀
    (fun coset : G ⧸ subgroup => (measurable.const_smul (Quotient.out coset)⁻¹).nullMeasurableSet)
    (subgroupCosetDomain_parts_aedisjoint subgroup fundamental)]
  apply tsum_congr
  intro coset
  exact (((measurePreserving_smul (Quotient.out coset)⁻¹ measure).restrict_image_emb
    (MeasurableEquiv.smul (Quotient.out coset)⁻¹).measurableEmbedding domain).lintegral_comp_emb
      (MeasurableEquiv.smul (Quotient.out coset)⁻¹).measurableEmbedding function).symm

theorem subgroupCosetDomain_integral {G X : Type*} [Group G] [Countable G]
    [MulAction G X] [MeasurableSpace X] [MeasurableConstSMul G X]
    (subgroup : Subgroup G) {domain : Set X} {measure : Measure X}
    [SMulInvariantMeasure G X measure]
    (measurable : MeasurableSet domain) (fundamental : IsFundamentalDomain G domain measure)
    {function : X → ℂ} (integrable : IntegrableOn function (subgroupCosetDomain subgroup domain) measure) :
    (∫ point in subgroupCosetDomain subgroup domain, function point ∂measure) =
      ∑' coset : G ⧸ subgroup, ∫ point in domain, function ((Quotient.out coset)⁻¹ • point) ∂measure := by
  rw [subgroupCosetDomain, integral_iUnion_ae
    (fun coset : G ⧸ subgroup => (measurable.const_smul (Quotient.out coset)⁻¹).nullMeasurableSet)
    (subgroupCosetDomain_parts_aedisjoint subgroup fundamental) integrable]
  apply tsum_congr
  intro coset
  exact (((measurePreserving_smul (Quotient.out coset)⁻¹ measure).restrict_image_emb
    (MeasurableEquiv.smul (Quotient.out coset)⁻¹).measurableEmbedding domain).integral_comp
      (MeasurableEquiv.smul (Quotient.out coset)⁻¹).measurableEmbedding function).symm

theorem subgroup_coset_integral_unfolding {G X : Type*} [Group G] [Countable G]
    [MulAction G X] [MeasurableSpace X] [MeasurableConstSMul G X]
    (subgroup : Subgroup G) {domain subgroupDomain : Set X} {measure : Measure X}
    [SMulInvariantMeasure G X measure]
    (domain_measurable : MeasurableSet domain) (fundamental : IsFundamentalDomain G domain measure)
    (subgroup_fundamental : IsFundamentalDomain subgroup subgroupDomain measure)
    {function : X → ℂ} (measurable : Measurable function)
    (invariant : ∀ element : subgroup, ∀ point, function (element • point) = function point)
    (finite : (∑' coset : G ⧸ subgroup, ∫⁻ point in domain,
      ‖function ((Quotient.out coset)⁻¹ • point)‖ₑ ∂measure) < ⊤) :
    IntegrableOn function subgroupDomain measure ∧
      (∑' coset : G ⧸ subgroup, ∫ point in domain,
        function ((Quotient.out coset)⁻¹ • point) ∂measure) =
        ∫ point in subgroupDomain, function point ∂measure := by
  have coset_fundamental := subgroupCosetDomain_isFundamental subgroup domain_measurable fundamental
  have coset_integrable : IntegrableOn function (subgroupCosetDomain subgroup domain) measure := by
    refine ⟨measurable.aestronglyMeasurable, ?_⟩
    change (∫⁻ point in subgroupCosetDomain subgroup domain, ‖function point‖ₑ ∂measure) < ⊤
    rw [subgroupCosetDomain_lintegral subgroup domain_measurable fundamental]
    exact finite
  refine ⟨(coset_fundamental.integrableOn_iff subgroup_fundamental invariant).mp coset_integrable, ?_⟩
  rw [← subgroupCosetDomain_integral subgroup domain_measurable fundamental coset_integrable]
  exact coset_fundamental.setIntegral_eq subgroup_fundamental invariant

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
