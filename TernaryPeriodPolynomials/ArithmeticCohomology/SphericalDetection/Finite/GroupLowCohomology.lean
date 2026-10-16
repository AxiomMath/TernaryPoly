module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyExactness

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G] [Finite G]

theorem finiteGroupH1_zero (representation : Rep ℂ G) (cohomology : groupCohomology.H1 representation) : cohomology = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective representation cohomology
  rw [groupCohomology.H1π_eq_zero_iff]
  refine ⟨-((Fintype.card G : ℂ)⁻¹) • ∑ element, cycle element, ?_⟩
  funext element
  have equation := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun other _ => oneCocycle_mul representation cycle element other)
  have reindex := Equiv.sum_comp (Equiv.mulLeft element) (fun other => cycle other)
  change (∑ other, cycle (element * other)) = ∑ other, cycle other at reindex
  rw [reindex, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ← map_sum (representation.ρ element)] at equation
  have difference : representation.ρ element (∑ other, cycle other) - ∑ other, cycle other =
      -(Fintype.card G : ℂ) • cycle element := by
    rw [neg_smul, Nat.cast_smul_eq_nsmul]
    linear_combination (norm := abel) -equation
  change representation.ρ element (-((Fintype.card G : ℂ)⁻¹) • ∑ other, cycle other) -
    -((Fintype.card G : ℂ)⁻¹) • ∑ other, cycle other = cycle element
  rw [map_smul, ← smul_sub, difference, smul_smul, neg_mul_neg,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := G)), one_smul]

theorem finiteGroupH2_zero (representation : Rep ℂ G) (cohomology : groupCohomology.H2 representation) : cohomology = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective representation cohomology
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun element => (Fintype.card G : ℂ)⁻¹ • ∑ other, cycle (element, other), ?_⟩
  funext pair
  have equation := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun other _ => twoCocycle_relation representation cycle pair.1 pair.2 other)
  have reindex := Equiv.sum_comp (Equiv.mulLeft pair.2) (fun other => cycle (pair.1, other))
  change (∑ other, cycle (pair.1, pair.2 * other)) = ∑ other, cycle (pair.1, other) at reindex
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    reindex, ← map_sum (representation.ρ pair.1)] at equation
  have difference : representation.ρ pair.1 (∑ other, cycle (pair.2, other)) -
      (∑ other, cycle (pair.1 * pair.2, other)) + (∑ other, cycle (pair.1, other)) =
      (Fintype.card G : ℂ) • cycle (pair.1, pair.2) := by
    rw [Nat.cast_smul_eq_nsmul]
    linear_combination (norm := abel) -equation
  change representation.ρ pair.1 ((Fintype.card G : ℂ)⁻¹ • ∑ other, cycle (pair.2, other)) -
    (Fintype.card G : ℂ)⁻¹ • (∑ other, cycle (pair.1 * pair.2, other)) +
    (Fintype.card G : ℂ)⁻¹ • (∑ other, cycle (pair.1, other)) = cycle (pair.1, pair.2)
  rw [map_smul, ← smul_sub, ← smul_add, difference, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := G)), one_smul]

theorem splitRestriction_injective_of_finite_quotient {N E L : Type} [Group N] [Group E] [Group L] [Finite L]
    {extension : GroupExtension N E L} (splitting : extension.Splitting) (representation : Rep ℂ E) :
    Function.Injective (twoCohomologyRestriction extension.inl representation) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro cohomology restricted_zero
  let relative : (twoCohomologyRestriction extension.inl representation).ker := ⟨cohomology, restricted_zero⟩
  have edge_zero : splitCohomologyEdge splitting representation relative = 0 :=
    finiteGroupH1_zero (splitRadicalH1Representation splitting representation) _
  obtain ⟨levi_class, equality⟩ := splitCohomologyEdge_kernel_inflation splitting representation relative edge_zero
  change splitInvariantInflation splitting representation levi_class = cohomology at equality
  rw [finiteGroupH2_zero (splitInvariantRepresentation splitting representation) levi_class, map_zero] at equality
  exact equality.symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
