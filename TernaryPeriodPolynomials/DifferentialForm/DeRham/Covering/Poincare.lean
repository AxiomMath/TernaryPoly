module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.LocalExtension

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- All-degree local exactness in the actual local-coefficient covering complex. Every quotient
point in a lifting chart has one neighborhood on which every positive-degree closed form has a
smooth equivariant primitive. The neighborhood and restriction are genuine quotient subsets. -/
theorem chart_local_poincare (S : Space) {q : OrbitSpace} (hq : q ∈ (quotientChart S).source) :
    ∃ V : Set OrbitSpace, ∃ hV : IsOpen V, q ∈ V ∧
      ∃ hVS : V ⊆ (quotientChart S).source,
        ∀ (n : ℕ) (w : EquivariantForm ρ (quotientChart S).source (n + 1)),
          differential ρ (quotientChart S).open_source (n + 1) w = 0 →
          ∃ z : EquivariantForm ρ V n,
            differential ρ hV n z = restrictEquivariant ρ hVS (n + 1) w := by
  let x := quotientChart S q
  have hx : x ∈ (quotientChart S).target := (quotientChart S).map_source hq
  obtain ⟨r, hr, hball, hprim⟩ := local_poincare (F := F) (quotientChart S).open_target hx
  refine ⟨chartOpen S (Metric.ball x r), chartOpen_isOpen S Metric.isOpen_ball,
    ⟨hq, Metric.mem_ball_self hr⟩, chartOpen_subset S _, fun n w hw => ?_⟩
  have hc : d (quotientChart S).open_target (n + 1) (chartRestrict ρ S (n + 1) w) = 0 := by
    rw [← chartRestrict_d, hw, map_zero]
  obtain ⟨z, hz⟩ := hprim n (chartRestrict ρ S (n + 1) w) hc
  refine ⟨chartExtendOn ρ S Metric.isOpen_ball n z, ?_⟩
  rw [chartExtendOn_d, hz, chartExtendOn_restrict ρ S Metric.isOpen_ball hball]

end TernaryPoly.SmoothCoveringDeRham
