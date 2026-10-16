module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.OrbitCoverIntegrals

@[expose] public section


open MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem orbit_quotient_preimage_image {G X : Type*} [Group G] [MulAction G X] (set : Set X) :
    (Quotient.mk (MulAction.orbitRel G X)) ⁻¹' ((Quotient.mk (MulAction.orbitRel G X)) '' set) =
      ⋃ element : G, element • set := by
  ext point
  constructor
  · rintro ⟨representative, member, equality⟩
    obtain ⟨element, represents⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact equality.symm))
    exact Set.mem_iUnion.mpr ⟨element, representative, member, represents⟩
  · intro member
    obtain ⟨element, representative, representative_member, equality⟩ := Set.mem_iUnion.mp member
    refine ⟨representative, representative_member, ?_⟩
    apply Eq.symm
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨element, equality⟩)

theorem orbit_quotient_image_measurable {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G]
    {set : Set X} (measurable : MeasurableSet set) :
    MeasurableSet ((Quotient.mk (MulAction.orbitRel G X)) '' set) := by
  apply measurableSet_quotient.mpr
  rw [orbit_quotient_preimage_image]
  exact MeasurableSet.iUnion (fun element => measurable.const_smul element)

theorem orbit_quotient_image_measure_le {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G]
    {measure : Measure X} [SMulInvariantMeasure G X measure] {domain set : Set X}
    (fundamental : IsFundamentalDomain G domain measure) (measurable : MeasurableSet set) :
    (Measure.map (Quotient.mk (MulAction.orbitRel G X)) (measure.restrict domain))
      ((Quotient.mk (MulAction.orbitRel G X)) '' set) ≤ measure set := by
  have image_measurable := orbit_quotient_image_measurable (G := G) measurable
  rw [Measure.map_apply measurable_quotient_mk'' image_measurable,
    Measure.restrict_apply (measurable_quotient_mk'' image_measurable),
    orbit_quotient_preimage_image, Set.iUnion_inter]
  exact (measure_iUnion_le _).trans_eq (fundamental.measure_eq_tsum set).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
