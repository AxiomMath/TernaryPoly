module

public import TernaryPeriodPolynomials.Analysis.Compact.ChartExtension

@[expose] public section


/-! An actual chart-supported quotient form is determined by its genuine chart representative. -/
noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
  SymmetricSpaceQuotientManifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {n : ℕ}

theorem eq_of_globalChartRepresentative_eq (w z : EquivariantForm ρ univ n)
    (hw : quotientSupport w ⊆ (quotientChart S).source)
    (hz : quotientSupport z ⊆ (quotientChart S).source)
    (he : globalChartRepresentative ρ S n w = globalChartRepresentative ρ S n z) : w = z := by
  have hr : restrictEquivariant ρ (subset_univ (quotientChart S).source) n w =
      restrictEquivariant ρ (subset_univ (quotientChart S).source) n z :=
    (chartTrivialization ρ S n).injective he
  apply Subtype.ext
  apply Form.ext
  intro x hx
  by_cases hq : coordinateProjection x ∈ (quotientChart S).source
  · have h := congrArg (fun a : EquivariantForm ρ (quotientChart S).source n =>
      (a.val : RawForm Coordinates F n) x) hr
    exact (restrictEquivariant_apply ρ (subset_univ (quotientChart S).source) w ⟨hx.1,hq⟩).symm.trans
      (h.trans (restrictEquivariant_apply ρ (subset_univ (quotientChart S).source) z ⟨hx.1,hq⟩))
  · have hw0 : (w.val : RawForm Coordinates F n) x = 0 := by
      by_contra hn
      exact hq (hw (subset_closure ⟨x,hn,rfl⟩))
    have hz0 : (z.val : RawForm Coordinates F n) x = 0 := by
      by_contra hn
      exact hq (hz (subset_closure ⟨x,hn,rfl⟩))
    exact hw0.trans hz0.symm

end TernaryPoly.SmoothCoveringDeRham
