module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Unfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem additiveDomain_translate_isFundamental (shift : Adeles) :
    IsAddFundamentalDomain rationalLattice ((fun value => shift + value) '' additiveDomain) adeleMeasure := by
  exact additiveDomain_isFundamental.vadd_of_comm shift

theorem rational_periodic_integral_add_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles → E)
    (periodic : ∀ rational : ℚ, ∀ value, function (rationalAdele rational + value) = function value)
    (shift : Adeles) :
    (∫ value in additiveDomain, function (shift + value) ∂adeleMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure := by
  have lattice_periodic (latticePoint : rationalLattice) (value : Adeles) :
      function (latticePoint +ᵥ value) = function value := by
    obtain ⟨rational, rational_spec⟩ := latticePoint.property
    change function (latticePoint.val + value) = function value
    rw [← rational_spec]
    exact periodic rational value
  calc
    _ = ∫ value in (fun value => shift + value) '' additiveDomain, function value ∂adeleMeasure :=
      ((measurePreserving_add_left adeleMeasure shift).setIntegral_image_emb
        (MeasurableEquiv.addLeft shift).measurableEmbedding function additiveDomain).symm
    _ = _ := (additiveDomain_translate_isFundamental shift).setIntegral_eq
      additiveDomain_isFundamental lattice_periodic

theorem rational_periodic_integral_sub_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles → E)
    (periodic : ∀ rational : ℚ, ∀ value, function (rationalAdele rational + value) = function value)
    (shift : Adeles) :
    (∫ value in additiveDomain, function (value - shift) ∂adeleMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure := by
  simpa only [sub_eq_add_neg, add_comm] using
    rational_periodic_integral_add_left function periodic (-shift)

theorem rational_periodic_integrableOn_add_left {E : Type*} [NormedAddCommGroup E]
    (function : Adeles → E)
    (periodic : ∀ rational : ℚ, ∀ value, function (rationalAdele rational + value) = function value)
    (integrable : IntegrableOn function additiveDomain adeleMeasure) (shift : Adeles) :
    IntegrableOn (fun value => function (shift + value)) additiveDomain adeleMeasure := by
  have lattice_periodic (latticePoint : rationalLattice) (value : Adeles) :
      function (latticePoint +ᵥ value) = function value := by
    obtain ⟨rational, rational_spec⟩ := latticePoint.property
    change function (latticePoint.val + value) = function value
    rw [← rational_spec]
    exact periodic rational value
  have translated_integrable :=
    (additiveDomain_isFundamental.integrableOn_iff
      (additiveDomain_translate_isFundamental shift) lattice_periodic).mp integrable
  exact ((measurePreserving_add_left adeleMeasure shift).integrableOn_image
    (MeasurableEquiv.addLeft shift).measurableEmbedding).mp translated_integrable

theorem rational_periodic_aestronglyMeasurable {E : Type*} [NormedAddCommGroup E]
    (function : Adeles → E)
    (periodic : ∀ rational : ℚ, ∀ value, function (rationalAdele rational + value) = function value)
    (integrable : IntegrableOn function additiveDomain adeleMeasure) :
    AEStronglyMeasurable function adeleMeasure := by
  have translates_cover :
      (⋃ rational : ℚ, (fun value => rationalAdele rational + value) '' additiveDomain) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro value
    obtain ⟨rational, rational_spec⟩ := rational_translate_mem_additiveDomain value
    apply Set.mem_iUnion.mpr
    refine ⟨rational, value - rationalAdele rational, rational_spec, ?_⟩
    abel_nf
  have on_translate (rational : ℚ) :
      AEStronglyMeasurable function
        (adeleMeasure.restrict ((fun value => rationalAdele rational + value) '' additiveDomain)) := by
    have shifted := rational_periodic_integrableOn_add_left function periodic integrable (rationalAdele rational)
    exact (((measurePreserving_add_left adeleMeasure (rationalAdele rational)).integrableOn_image
      (MeasurableEquiv.addLeft (rationalAdele rational)).measurableEmbedding).mpr shifted).aestronglyMeasurable
  have measurable_union := AEStronglyMeasurable.iUnion on_translate
  rw [translates_cover, Measure.restrict_univ] at measurable_union
  exact measurable_union

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
