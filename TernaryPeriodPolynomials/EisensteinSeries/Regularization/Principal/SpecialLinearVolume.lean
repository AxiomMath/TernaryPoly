module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.SpecialLinear

@[expose] public section


open Matrix MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def principalRealSpecialLinearCover : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  ⋃ residue : integerSpecialLinearReduction.range,
    (SpecialLinearGroup.map (Int.castRingHom ℝ) (integerSpecialLinearReductionRepresentative residue))⁻¹ •
      realSpecialLinearReducedCover

theorem principalRealSpecialLinearCover_orbit (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    ∃ principal : principalRealSpecialLinear, principal • matrix ∈ principalRealSpecialLinearCover := by
  obtain ⟨integral, rotation, orthogonal, reduced, positive⟩ := specialLinear_integral_real_reduction matrix
  have in_cover : SpecialLinearGroup.map (Int.castRingHom ℝ) integral * matrix ∈ realSpecialLinearReducedCover :=
    ⟨_, rotation⁻¹, reduced, positive, realSpecialOrthogonal_inv orthogonal, by simp [mul_assoc]⟩
  obtain ⟨residue, principal, factor⟩ := integerSpecialLinearReduction_factor integral
  refine ⟨⟨SpecialLinearGroup.map (Int.castRingHom ℝ) principal.val,
    ⟨principal.val, principal.property, rfl⟩⟩, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨residue, ⟨SpecialLinearGroup.map (Int.castRingHom ℝ) integral * matrix, in_cover, ?_⟩⟩
  change (SpecialLinearGroup.map (Int.castRingHom ℝ) (integerSpecialLinearReductionRepresentative residue))⁻¹ *
    (SpecialLinearGroup.map (Int.castRingHom ℝ) integral * matrix) =
      SpecialLinearGroup.map (Int.castRingHom ℝ) principal.val * matrix
  rw [factor, map_mul, mul_assoc, inv_mul_cancel_left]

theorem principalRealSpecialLinearCover_iUnion :
    (⋃ principal : principalRealSpecialLinear, principal • principalRealSpecialLinearCover) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro matrix
  obtain ⟨principal, member⟩ := principalRealSpecialLinearCover_orbit matrix
  exact Set.mem_iUnion.mpr ⟨principal⁻¹, ⟨principal • matrix, member, inv_smul_smul principal matrix⟩⟩

theorem principalRealSpecialLinearCover_measure_finite : realSpecialLinearHaar principalRealSpecialLinearCover < ⊤ := by
  let : Fintype integerSpecialLinearReduction.range := Fintype.ofFinite _
  apply lt_of_le_of_lt (measure_iUnion_le _)
  simp only [measure_smul, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_lt_top (by finiteness) realSpecialLinearReducedCover_measure_finite

theorem principalRealSpecialLinear_measurable_domain :
    ∃ domain : Set (SpecialLinearGroup (Fin 3) ℝ), MeasurableSet domain ∧
      IsFundamentalDomain principalRealSpecialLinear domain realSpecialLinearHaar :=
  discrete_subgroup_measurable_fundamental_domain principalRealSpecialLinear realSpecialLinearHaar

noncomputable def principalRealSpecialLinearDomain : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  Classical.choose principalRealSpecialLinear_measurable_domain

theorem principalRealSpecialLinearDomain_measurable : MeasurableSet principalRealSpecialLinearDomain :=
  (Classical.choose_spec principalRealSpecialLinear_measurable_domain).1

theorem principalRealSpecialLinearDomain_fundamental :
    IsFundamentalDomain principalRealSpecialLinear principalRealSpecialLinearDomain realSpecialLinearHaar :=
  (Classical.choose_spec principalRealSpecialLinear_measurable_domain).2

theorem principalRealSpecialLinearDomain_measure_finite : realSpecialLinearHaar principalRealSpecialLinearDomain < ⊤ :=
  lt_of_le_of_lt (fundamental_domain_measure_le_orbit_cover principalRealSpecialLinearDomain_fundamental
    principalRealSpecialLinearCover_iUnion) principalRealSpecialLinearCover_measure_finite

instance principalRealSpecialLinearDomain_restrict_finite :
    IsFiniteMeasure (realSpecialLinearHaar.restrict principalRealSpecialLinearDomain) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact principalRealSpecialLinearDomain_measure_finite

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
