module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ChartIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def radicalLatticeEquiv : ℚ × ℚ ≃ rationalLattice.prod rationalLattice :=
  (rationalLatticeEquiv.prodCongr rationalLatticeEquiv).trans
    (rationalLattice.prodEquiv rationalLattice).toEquiv.symm

instance radicalLattice_countable : Countable (rationalLattice.prod rationalLattice) :=
  Function.Injective.countable radicalLatticeEquiv.symm.injective

theorem radicalLatticeEquiv_neg_vadd (rational : ℚ × ℚ) (coordinates : Adeles × Adeles) :
    -radicalLatticeEquiv rational +ᵥ coordinates =
      (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2) := by
  change (-rationalAdele rational.1 + coordinates.1, -rationalAdele rational.2 + coordinates.2) = _
  simp only [sub_eq_add_neg, add_comm]

theorem radical_domain_unique_translate (coordinates : Adeles × Adeles) :
    ∃! latticePoint : rationalLattice.prod rationalLattice,
      latticePoint +ᵥ coordinates ∈ additiveDomain ×ˢ additiveDomain := by
  obtain ⟨first, first_spec⟩ := rational_translate_mem_additiveDomain coordinates.1
  obtain ⟨second, second_spec⟩ := rational_translate_mem_additiveDomain coordinates.2
  refine ⟨⟨(rationalAdele (-first), rationalAdele (-second)),
    ⟨⟨-first, rfl⟩, ⟨-second, rfl⟩⟩⟩, ?_, ?_⟩
  · change rationalAdele (-first) + coordinates.1 ∈ additiveDomain ∧
      rationalAdele (-second) + coordinates.2 ∈ additiveDomain
    simpa only [map_neg, sub_eq_add_neg, add_comm] using And.intro first_spec second_spec
  · intro other other_spec
    obtain ⟨otherFirst, first_value⟩ := other.property.1
    obtain ⟨otherSecond, second_value⟩ := other.property.2
    change rationalAdele otherFirst = other.val.1 at first_value
    change rationalAdele otherSecond = other.val.2 at second_value
    change other.val.1 + coordinates.1 ∈ additiveDomain ∧
      other.val.2 + coordinates.2 ∈ additiveDomain at other_spec
    have first_translate : coordinates.1 - rationalAdele (-otherFirst) ∈ additiveDomain := by
      simpa only [map_neg, sub_neg_eq_add, add_comm, first_value] using other_spec.1
    have second_translate : coordinates.2 - rationalAdele (-otherSecond) ∈ additiveDomain := by
      simpa only [map_neg, sub_neg_eq_add, add_comm, second_value] using other_spec.2
    have first_equal := rational_translate_unique coordinates.1 first_translate first_spec
    have second_equal := rational_translate_unique coordinates.2 second_translate second_spec
    apply Subtype.ext
    apply Prod.ext
    · change other.val.1 = rationalAdele (-first)
      rw [← first_equal, neg_neg]
      exact first_value.symm
    · change other.val.2 = rationalAdele (-second)
      rw [← second_equal, neg_neg]
      exact second_value.symm

theorem radicalDomain_isFundamental :
    IsAddFundamentalDomain (rationalLattice.prod rationalLattice)
      (additiveDomain ×ˢ additiveDomain) radicalMeasure := by
  have measurable : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  exact IsAddFundamentalDomain.mk' (measurable.prod measurable).nullMeasurableSet
    radical_domain_unique_translate

theorem radical_integral_eq_rational_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles × Adeles → E) (integrable : Integrable function radicalMeasure) :
    (∫ coordinates, function coordinates ∂radicalMeasure) =
      ∑' rational : ℚ × ℚ, ∫ coordinates : Adeles × Adeles,
        function (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2)
          ∂planeDomainMeasure := by
  rw [radicalDomain_isFundamental.integral_eq_tsum' function integrable]
  simpa only [planeDomainMeasure_eq, radicalLatticeEquiv_neg_vadd] using
    (radicalLatticeEquiv.tsum_eq (fun latticePoint : rationalLattice.prod rationalLattice =>
      ∫ coordinates in additiveDomain ×ˢ additiveDomain,
        function (-latticePoint +ᵥ coordinates) ∂radicalMeasure)).symm

theorem radical_lintegral_eq_rational_tsum (function : Adeles × Adeles → ENNReal) :
    (∫⁻ coordinates, function coordinates ∂radicalMeasure) =
      ∑' rational : ℚ × ℚ, ∫⁻ coordinates : Adeles × Adeles,
        function (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2)
          ∂planeDomainMeasure := by
  rw [radicalDomain_isFundamental.lintegral_eq_tsum' function]
  simpa only [planeDomainMeasure_eq, radicalLatticeEquiv_neg_vadd] using
    (radicalLatticeEquiv.tsum_eq (fun latticePoint : rationalLattice.prod rationalLattice =>
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        function (-latticePoint +ᵥ coordinates) ∂radicalMeasure)).symm

theorem radical_translate_integrable (function : Adeles × Adeles → ℂ)
    (integrable : Integrable function radicalMeasure) (rational : ℚ × ℚ) :
    Integrable (fun coordinates : Adeles × Adeles =>
      function (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2))
        planeDomainMeasure := by
  rw [planeDomainMeasure_eq]
  simpa only [sub_eq_add_neg, Prod.add_def] using
    (integrable.comp_add_right (-rationalAdele rational.1, -rationalAdele rational.2)).restrict

theorem radical_periodization_integrable (function : Adeles × Adeles → ℂ)
    (integrable : Integrable function radicalMeasure) :
    Integrable (fun coordinates : Adeles × Adeles => ∑' rational : ℚ × ℚ,
      function (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2))
        planeDomainMeasure := by
  apply integrable_tsum_of_enorm_sum
  · intro rational
    exact (radical_translate_integrable function integrable rational).aestronglyMeasurable
  · rw [← radical_lintegral_eq_rational_tsum (fun coordinates => ‖function coordinates‖ₑ)]
    exact integrable.hasFiniteIntegral.ne

theorem radical_periodization_integral (function : Adeles × Adeles → ℂ)
    (integrable : Integrable function radicalMeasure) :
    (∫ coordinates : Adeles × Adeles, ∑' rational : ℚ × ℚ,
      function (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2)
        ∂planeDomainMeasure) = ∫ coordinates, function coordinates ∂radicalMeasure := by
  have term_measurable (rational : ℚ × ℚ) :=
    (radical_translate_integrable function integrable rational).aestronglyMeasurable
  have norm_sum_finite : (∑' rational : ℚ × ℚ, ∫⁻ coordinates : Adeles × Adeles,
      ‖function (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2)‖ₑ
        ∂planeDomainMeasure) ≠ ⊤ := by
    rw [← radical_lintegral_eq_rational_tsum (fun coordinates => ‖function coordinates‖ₑ)]
    exact integrable.hasFiniteIntegral.ne
  rw [integral_tsum term_measurable norm_sum_finite]
  exact (radical_integral_eq_rational_tsum function integrable).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
