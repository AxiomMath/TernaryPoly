module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Unfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem radicalDomain_image_isFundamental (equivalence : (Adeles × Adeles) ≃ₜ+ (Adeles × Adeles))
    (stable : ∀ coordinates ∈ rationalLattice.prod rationalLattice,
      equivalence coordinates ∈ rationalLattice.prod rationalLattice)
    (inverse_stable : ∀ coordinates ∈ rationalLattice.prod rationalLattice,
      equivalence.symm coordinates ∈ rationalLattice.prod rationalLattice) :
    IsAddFundamentalDomain (rationalLattice.prod rationalLattice)
      (equivalence '' (additiveDomain ×ˢ additiveDomain)) radicalMeasure := by
  have measurable : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  have image_measurable := equivalence.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
    (measurable.prod measurable)
  apply IsAddFundamentalDomain.mk' image_measurable.nullMeasurableSet
  intro coordinates
  obtain ⟨latticePoint, point_spec, unique⟩ := radical_domain_unique_translate (equivalence.symm coordinates)
  refine ⟨⟨equivalence latticePoint.val, stable _ latticePoint.property⟩, ?_, ?_⟩
  · refine ⟨latticePoint.val + equivalence.symm coordinates, point_spec, ?_⟩
    change equivalence (latticePoint.val + equivalence.symm coordinates) =
      equivalence latticePoint.val + coordinates
    rw [map_add, equivalence.apply_symm_apply]
  · intro other other_spec
    let preimage : rationalLattice.prod rationalLattice :=
      ⟨equivalence.symm other.val, inverse_stable _ other.property⟩
    have preimage_spec : preimage +ᵥ equivalence.symm coordinates ∈ additiveDomain ×ˢ additiveDomain := by
      obtain ⟨value, value_mem, value_eq⟩ := other_spec
      change equivalence value = other.val + coordinates at value_eq
      change equivalence.symm other.val + equivalence.symm coordinates ∈ additiveDomain ×ˢ additiveDomain
      rw [← map_add, ← value_eq, equivalence.symm_apply_apply]
      exact value_mem
    have equal := congrArg (fun point : rationalLattice.prod rationalLattice => equivalence point.val)
      (unique preimage preimage_spec)
    apply Subtype.ext
    simpa only [preimage, equivalence.apply_symm_apply] using equal

theorem radical_lattice_automorphism_measurePreserving
    (equivalence : (Adeles × Adeles) ≃ₜ+ (Adeles × Adeles))
    (stable : ∀ coordinates ∈ rationalLattice.prod rationalLattice,
      equivalence coordinates ∈ rationalLattice.prod rationalLattice)
    (inverse_stable : ∀ coordinates ∈ rationalLattice.prod rationalLattice,
      equivalence.symm coordinates ∈ rationalLattice.prod rationalLattice) :
    MeasurePreserving equivalence radicalMeasure radicalMeasure := by
  have image_fundamental := radicalDomain_image_isFundamental equivalence stable inverse_stable
  have domain_measure : radicalMeasure (additiveDomain ×ˢ additiveDomain) = 1 := by
    rw [radicalMeasure, Measure.prod_prod, adeleMeasure_additiveDomain, one_mul]
  have image_measure : radicalMeasure (equivalence '' (additiveDomain ×ˢ additiveDomain)) = 1 :=
    (image_fundamental.measure_eq radicalDomain_isFundamental).trans domain_measure
  have scale := addEquivAddHaarChar_smul_preimage radicalMeasure
    (X := equivalence '' (additiveDomain ×ˢ additiveDomain)) equivalence
  rw [Set.preimage_image_eq _ equivalence.injective, domain_measure, image_measure] at scale
  have char_one : addEquivAddHaarChar equivalence = 1 := by
    change (addEquivAddHaarChar equivalence : ENNReal) * 1 = 1 at scale
    rw [mul_one] at scale
    exact ENNReal.coe_injective scale
  refine ⟨equivalence.continuous.measurable, ?_⟩
  have map_scale := addEquivAddHaarChar_smul_map radicalMeasure equivalence
  simpa only [char_one, one_smul] using map_scale

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
