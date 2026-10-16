module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SubgroupCosetUnfolding
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section


open MeasureTheory
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem orbitCosetRepresentative_injective {G I : Type*} [Group G] [MulAction G I] (point : I) :
    Function.Injective (fun coset : G ⧸ MulAction.stabilizer G point => Quotient.out coset • point) := by
  have identity (coset : G ⧸ MulAction.stabilizer G point) :
      ((MulAction.orbitEquivQuotientStabilizer G point).symm coset).val = Quotient.out coset • point := by
    nth_rw 1 [← QuotientGroup.out_eq' coset]
    exact MulAction.orbitEquivQuotientStabilizer_symm_apply G point _
  intro first second equal
  apply (MulAction.orbitEquivQuotientStabilizer G point).symm.injective
  apply Subtype.ext
  simpa only [identity] using equal

theorem orbitSigmaEquiv_symm_apply {G I : Type*} [Group G] [MulAction G I]
    (orbit : Quotient (MulAction.orbitRel G I)) (coset : G ⧸ MulAction.stabilizer G orbit.out) :
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G I).symm ⟨orbit, coset⟩ =
      Quotient.out coset • orbit.out := by
  change ((MulAction.orbitEquivQuotientStabilizer G orbit.out).symm coset).val = _
  nth_rw 1 [← QuotientGroup.out_eq' coset]
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply G orbit.out _

theorem summable_tsum_by_action_orbits {G I : Type*} [Group G] [MulAction G I]
    {function : I → ℂ} (summable : Summable function) :
    (∑' point, function point) =
      ∑' orbit : Quotient (MulAction.orbitRel G I),
        ∑' coset : G ⧸ MulAction.stabilizer G orbit.out, function (Quotient.out coset • orbit.out) := by
  let equivalence := MulAction.selfEquivSigmaOrbitsQuotientStabilizer G I
  have indexed : Summable (function ∘ equivalence.symm) := equivalence.symm.summable_iff.mpr summable
  have sum_sigma := indexed.tsum_sigma
  dsimp only [Function.comp_def] at sum_sigma
  rw [← equivalence.symm.tsum_eq function, sum_sigma]
  simp only [equivalence, orbitSigmaEquiv_symm_apply]

theorem flag_orbit_pairing_unfolding_zero
    {G I X : Type*} [Group G] [Countable G] [MulAction G I] [MulAction G X]
    [MeasurableSpace X] [MeasurableConstSMul G X] {measure : Measure X}
    [SMulInvariantMeasure G X measure]
    {domain : Set X} (domain_measurable : MeasurableSet domain)
    (fundamental : IsFundamentalDomain G domain measure)
    (orbitDomain : I → Set X)
    (orbit_fundamental : ∀ point, IsFundamentalDomain (MulAction.stabilizer G point) (orbitDomain point) measure)
    {family : I → X → ℂ} (measurable : ∀ point, Measurable (family point))
    (equivariant : ∀ element : G, ∀ point matrix, family point (element • matrix) = family (element⁻¹ • point) matrix)
    (finite : (∑' point, ∫⁻ matrix in domain, ‖family point matrix‖ₑ ∂measure) < ⊤)
    (zero : ∀ point, (∫ matrix in orbitDomain point, family point matrix ∂measure) = 0) :
    (∑' point, ∫ matrix in domain, family point matrix ∂measure) = 0 := by
  have summable : Summable (fun point => ∫ matrix in domain, family point matrix ∂measure) := by
    apply Summable.of_enorm
    apply ne_of_lt
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun point => enorm_integral_le_lintegral_enorm _)) finite
  rw [summable_tsum_by_action_orbits (G := G) summable]
  suffices each : ∀ orbit : Quotient (MulAction.orbitRel G I),
      (∑' coset : G ⧸ MulAction.stabilizer G orbit.out,
        ∫ matrix in domain, family (Quotient.out coset • orbit.out) matrix ∂measure) = 0 by
    simp only [each, tsum_zero]
  intro orbit
  have invariant (element : MulAction.stabilizer G orbit.out) (matrix : X) :
      family orbit.out (element • matrix) = family orbit.out matrix := by
    rw [Subgroup.smul_def, equivariant]
    have fixed : element.val⁻¹ • orbit.out = orbit.out := element⁻¹.property
    rw [fixed]
  have bound : (∑' coset : G ⧸ MulAction.stabilizer G orbit.out, ∫⁻ matrix in domain,
      ‖family orbit.out ((Quotient.out coset)⁻¹ • matrix)‖ₑ ∂measure) < ⊤ := by
    simp only [equivariant, inv_inv]
    exact lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective (orbitCosetRepresentative_injective orbit.out)
      (fun point => ∫⁻ matrix in domain, ‖family point matrix‖ₑ ∂measure)) finite
  have unfolded := subgroup_coset_integral_unfolding (MulAction.stabilizer G orbit.out)
    domain_measurable fundamental (orbit_fundamental orbit.out) (measurable orbit.out) invariant bound
  simpa only [equivariant, inv_inv, zero] using unfolded.2

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
