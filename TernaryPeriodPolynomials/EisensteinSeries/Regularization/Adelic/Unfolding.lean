module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.FundamentalDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def rationalLatticeEquiv : ℚ ≃ rationalLattice :=
  Equiv.ofBijective (fun rational => ⟨rationalAdele rational, ⟨rational, rfl⟩⟩)
    ⟨fun _ _ equal => rationalAdele_injective (congrArg Subtype.val equal), by
      rintro ⟨_, rational, equality⟩
      exact ⟨rational, Subtype.ext equality⟩⟩

instance rationalLattice_countable : Countable rationalLattice :=
  Function.Injective.countable rationalLatticeEquiv.symm.injective

theorem adele_integral_eq_rational_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles → E) (integrable : Integrable function adeleMeasure) :
    (∫ value, function value ∂adeleMeasure) =
      ∑' rational : ℚ, ∫ value in additiveDomain, function (rationalAdele rational + value) ∂adeleMeasure := by
  rw [additiveDomain_isFundamental.integral_eq_tsum'' function integrable]
  exact (rationalLatticeEquiv.tsum_eq
    (fun latticePoint : rationalLattice =>
      ∫ value in additiveDomain, function (latticePoint.val + value) ∂adeleMeasure)).symm

theorem adele_lintegral_eq_rational_tsum (function : Adeles → ENNReal) :
    (∫⁻ value, function value ∂adeleMeasure) =
      ∑' rational : ℚ, ∫⁻ value in additiveDomain, function (rationalAdele rational + value) ∂adeleMeasure := by
  rw [additiveDomain_isFundamental.lintegral_eq_tsum'' function]
  exact (rationalLatticeEquiv.tsum_eq
    (fun latticePoint : rationalLattice =>
      ∫⁻ value in additiveDomain, function (latticePoint.val + value) ∂adeleMeasure)).symm

theorem rational_periodization_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles → E) (integrable : Integrable function adeleMeasure) :
    (∫ value in additiveDomain, ∑' rational : ℚ,
      function (rationalAdele rational + value) ∂adeleMeasure) =
      ∫ value, function value ∂adeleMeasure := by
  have term_measurable (rational : ℚ) : AEStronglyMeasurable
      (fun value => function (rationalAdele rational + value)) (adeleMeasure.restrict additiveDomain) :=
    (integrable.comp_add_left (rationalAdele rational)).restrict.aestronglyMeasurable
  have sum_finite : (∑' rational : ℚ, ∫⁻ value in additiveDomain,
      ‖function (rationalAdele rational + value)‖ₑ ∂adeleMeasure) ≠ ⊤ := by
    rw [← adele_lintegral_eq_rational_tsum (fun value => ‖function value‖ₑ)]
    exact integrable.hasFiniteIntegral.ne
  rw [integral_tsum term_measurable sum_finite]
  exact (adele_integral_eq_rational_tsum function integrable).symm

theorem rational_periodization_shift_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles → E) (integrable : Integrable function adeleMeasure) (shift : Adeles) :
    (∫ value in additiveDomain, ∑' rational : ℚ,
      function (value - rationalAdele rational - shift) ∂adeleMeasure) =
      ∫ value, function value ∂adeleMeasure := by
  have shifted_integrable : Integrable (fun value => function (value - shift)) adeleMeasure := by
    simpa only [sub_eq_add_neg] using integrable.comp_add_right (-shift)
  calc
    _ = ∫ value in additiveDomain, ∑' rational : ℚ,
        function (rationalAdele rational + value - shift) ∂adeleMeasure := by
      apply integral_congr_ae
      filter_upwards with value
      simpa only [Equiv.neg_apply, map_neg, sub_neg_eq_add, add_comm] using
        ((Equiv.neg ℚ).tsum_eq (fun rational => function (value - rationalAdele rational - shift))).symm
    _ = ∫ value, function (value - shift) ∂adeleMeasure :=
      rational_periodization_integral _ shifted_integrable
    _ = _ := integral_sub_right_eq_self function shift

theorem rational_periodization_fiber_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles → Adeles → E) (shift : Adeles → Adeles)
    (integrable : Integrable (Function.uncurry function)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ first in additiveDomain, ∫ second in additiveDomain,
      ∑' rational : ℚ, function first (second - rationalAdele rational - shift first)
        ∂adeleMeasure ∂adeleMeasure) =
      ∫ second, ∫ first in additiveDomain, function first second ∂adeleMeasure ∂adeleMeasure := by
  calc
    _ = ∫ first in additiveDomain, ∫ second, function first second ∂adeleMeasure ∂adeleMeasure := by
      apply integral_congr_ae
      filter_upwards [integrable.prod_right_ae] with first first_integrable
      exact rational_periodization_shift_integral (function first) first_integrable (shift first)
    _ = _ := integral_integral_swap integrable

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
