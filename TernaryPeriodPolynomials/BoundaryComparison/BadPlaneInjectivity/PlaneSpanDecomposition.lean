module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs

@[expose] public section


/-!
# The plane span as a supremum of per-datum summands, and its finite-sum decomposition

`Argument.Defs.Spanning.automorphicPlaneSpan n` is defined as the `Submodule.span` of the union,
over all `D : CohomologicalCuspData n`, of the carriers of the per-datum submodules
`boundarySummand D.inducingData .plane`. Since each of those is *already* a submodule of the same
ambient space `StratumH2 n trivialCharacter .plane`, the span of their union is simply their
supremum, and membership in that supremum unfolds (`Submodule.mem_iSup_iff_exists_finsupp`) to a
finite-sum decomposition: a vector lies in `automorphicPlaneSpan n` iff it is a finite sum of
vectors drawn one at a time from the individual per-datum summands.

This is unconditional, elementary Mathlib bookkeeping (`Submodule.span_iUnion` + `Submodule.span_eq`
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous


namespace TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

noncomputable def planeSummandFamily (n : ℕ) :
    CohomologicalCuspData n → Submodule ℂ (StratumH2 n trivialCharacter .plane) :=
  fun D => boundarySummand D.inducingData .plane

/-- `automorphicPlaneSpan n` is the supremum of the per-datum plane summands, not merely their
span-of-a-union: each summand is already a submodule, so spanning the union adds nothing. -/
theorem automorphicPlaneSpan_eq_iSup (n : ℕ) :
    automorphicPlaneSpan n = ⨆ D : CohomologicalCuspData n, planeSummandFamily n D := by
  have hset : {ξ : StratumH2 n trivialCharacter .plane |
      ∃ D : CohomologicalCuspData n, ξ ∈ boundarySummand D.inducingData .plane} =
      ⋃ D : CohomologicalCuspData n, (planeSummandFamily n D : Set _) := by
    ext ξ; simp [Set.mem_iUnion, planeSummandFamily]
  unfold automorphicPlaneSpan
  rw [hset, Submodule.span_iUnion]
  simp [planeSummandFamily]

/-- **Finite-sum decomposition of the plane span.** A vector lying in `automorphicPlaneSpan n` is
a finite sum of vectors, one drawn from each of finitely many per-datum plane summands. This is
exactly the shape of decomposition that `bad_plane_data_injective`'s odd case needs for its own `ξ`, once
`Targets.bad_plane_cuspidal_span` supplies `ξ ∈ automorphicPlaneSpan n`. -/
theorem exists_finsupp_of_mem_automorphicPlaneSpan (n : ℕ)
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : ξ ∈ automorphicPlaneSpan n) :
    ∃ f : CohomologicalCuspData n →₀ StratumH2 n trivialCharacter .plane,
      (∀ D, f D ∈ planeSummandFamily n D) ∧
        (f.sum fun _ x => x) = ξ := by
  rw [automorphicPlaneSpan_eq_iSup] at hξ
  exact (Submodule.mem_iSup_iff_exists_finsupp (planeSummandFamily n) ξ).mp hξ

example (n : ℕ) (D : CohomologicalCuspData n) :
    planeSummandFamily n D = boundarySummand D.inducingData .plane := rfl

end TernaryPeriodPolynomials.Argument.BadPlaneInjectivity
