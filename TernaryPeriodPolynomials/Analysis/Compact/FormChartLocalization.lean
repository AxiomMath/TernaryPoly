module

public import TernaryPeriodPolynomials.Analysis.Compact.FormFiniteCharts

@[expose] public section


/-! Compact linear functionals are determined by their restrictions to single charts. -/
noncomputable section
namespace TernaryPoly.CompactFormFiniteCharts
open SymmetricSpacePositive SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open SmoothCoveringDeRham Set

/-- A linear functional vanishing on all chart-supported compact forms vanishes globally. -/
theorem functional_eq_zero {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : Representation ℝ DeckGroup F) (k : ℕ)
    (L : CompactSupportForm ρ univ k →ₗ[ℝ] ℝ)
    (hL : ∀ (S : Space) (f : CompactSupportForm ρ univ k),
      quotientSupport f.val ⊆ (quotientChart S).source → L f = 0)
    (f : CompactSupportForm ρ univ k) : L f = 0 := by
  obtain ⟨s, a, ha, hsum⟩ := exists_finite_chart_decomposition ρ k f
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero (fun S _ => hL S.val (a S) (ha S))

end TernaryPoly.CompactFormFiniteCharts
