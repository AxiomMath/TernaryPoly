module

public import TernaryPeriodPolynomials.ModularForm.Periods.PeriodTenDimension
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenLinearIndependence
public import TernaryPeriodPolynomials.Polynomial.RestrictionEquiv

@[expose] public section


/-!
# The dimension of `solutionSpace F 10` is exactly two, and its span description

`TernaryPeriodPolynomials.Argument.RouteIndependent.restrictionEquiv F 10 : solutionSpace F 10 ≃ₗ[F] periodSpace F 10`
(`Proofs/RouteIndependent/RestrictionEquivNew.lean`, the route-independent mirror of
`TernaryPoly.Paper.restrictionEquiv`) transports the already-proved
`periodSpace_ten_finrank_eq_two` directly to `solutionSpace`, for every `Field F` `[CharZero F]`:
`LinearEquiv.finrank_eq` is unconditional, so no ℚ-specific detour (unlike `periodSpace`'s own
dimension fact) is needed here.

Combined with the membership of `symmetricTenSolution F`/`alternatingTenSolution F` in
`solutionSpace F 10` (via `cyclicLift_homogeneous`/`cyclicLift_solution`, applied to the already-
proved `symmetricTenPeriod_isHomogeneous`/`symmetricTenPeriod_periodRelations` etc. from
`ExampleDegreeTenAlgebra.lean`) and the linear independence of the same pair
(`linearIndependent_tenSolution`, from `ExampleDegreeTenLinearIndependence.lean`), the generic
Mathlib finishing lemma `Submodule.eq_of_le_of_finrank_le` gives the span description
`solutionSpace_ten_eq_span`, completing the last clause of `example_degree_ten`'s first conjunct
(Gap E).
-/


open MvPolynomial TernaryPoly.Paper TernaryPeriodPolynomials.Argument

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspForms

private theorem range_pair_eq' {α : Type*} (a b : α) :
    Set.range (![a, b] : Fin 2 → α) = ({a, b} : Set α) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

end TernaryPeriodPolynomials.Argument.CuspForms

namespace TernaryPeriodPolynomials.Argument

open TernaryPeriodPolynomials.Argument.CuspForms

variable (F : Type*) [Field F] [CharZero F]

/-- **Dimension of `solutionSpace` in degree ten.** Transported directly from
`periodSpace_ten_finrank_eq_two` via `TernaryPeriodPolynomials.Argument.RouteIndependent.restrictionEquiv`. -/
theorem solutionSpace_ten_finrank_eq_two :
    Module.finrank F (solutionSpace F 10) = 2 := by
  rw [LinearEquiv.finrank_eq (TernaryPeriodPolynomials.Argument.RouteIndependent.restrictionEquiv F 10)]
  exact periodSpace_ten_finrank_eq_two F

omit [CharZero F] in
theorem symmetricTenSolution_mem_solutionSpace :
    symmetricTenSolution F ∈ solutionSpace F 10 := by
  rw [symmetricTenSolution]
  exact ⟨cyclicLift_homogeneous symmetricTenPeriod_isHomogeneous,
    cyclicLift_solution symmetricTenPeriod_periodRelations⟩

omit [CharZero F] in
theorem alternatingTenSolution_mem_solutionSpace :
    alternatingTenSolution F ∈ solutionSpace F 10 := by
  rw [alternatingTenSolution]
  exact ⟨cyclicLift_homogeneous alternatingTenPeriod_isHomogeneous,
    cyclicLift_solution alternatingTenPeriod_periodRelations⟩

/-- **Span description of `solutionSpace` in degree ten (Gap E).** `solutionSpace F 10` is
exactly the span of `symmetricTenSolution F` and `alternatingTenSolution F`: both lie in it
(`symmetricTenSolution_mem_solutionSpace`/`alternatingTenSolution_mem_solutionSpace`) and are
linearly independent (`linearIndependent_tenSolution`), so their span already has the full
dimension `2` of the ambient space (`solutionSpace_ten_finrank_eq_two`). -/
theorem solutionSpace_ten_eq_span :
    Submodule.span F {symmetricTenSolution F, alternatingTenSolution F} = solutionSpace F 10 := by
  have hspan : Submodule.span F {symmetricTenSolution F, alternatingTenSolution F} ≤
      solutionSpace F 10 := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact symmetricTenSolution_mem_solutionSpace F
    · rw [hx]; exact alternatingTenSolution_mem_solutionSpace F
  have hrank : Module.finrank F
      (Submodule.span F {symmetricTenSolution F, alternatingTenSolution F}) = 2 := by
    rw [← range_pair_eq' (symmetricTenSolution F) (alternatingTenSolution F),
      finrank_span_eq_card (linearIndependent_tenSolution F), Fintype.card_fin]
  have : Module.Finite F (solutionSpace F 10) :=
    Module.finite_of_finrank_pos (by rw [solutionSpace_ten_finrank_eq_two F]; norm_num)
  exact Submodule.eq_of_le_of_finrank_le hspan (by rw [solutionSpace_ten_finrank_eq_two F, hrank])

end TernaryPeriodPolynomials.Argument
