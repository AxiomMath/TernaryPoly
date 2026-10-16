module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.OpenCharts

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace}

/-- Local exactness on every actual quotient open set, with genuine equivariant primitives
and restriction in the local-coefficient de Rham complex. -/
theorem quotient_local_poincare (hU : IsOpen U) {q : OrbitSpace} (hq : q ∈ U) :
    ∃ V : Set OrbitSpace, ∃ hV : IsOpen V, q ∈ V ∧ ∃ hVU : V ⊆ U,
      ∀ (n : ℕ) (w : EquivariantForm ρ U (n + 1)), differential ρ hU (n + 1) w = 0 →
        ∃ z : EquivariantForm ρ V n,
          differential ρ hV n z = restrictEquivariant ρ hVU (n + 1) w := by
  obtain ⟨S, hqS⟩ := quotientCharts_cover q
  let x := quotientChart S q
  have hx : x ∈ chartDomain S U :=
    ⟨(quotientChart S).map_source hqS, by simpa only [mem_preimage, x, (quotientChart S).left_inv hqS] using hq⟩
  obtain ⟨r, hr, hball, hprim⟩ := local_poincare (F := F) (chartDomain_isOpen S hU) hx
  refine ⟨chartOpen S (Metric.ball x r), chartOpen_isOpen S Metric.isOpen_ball,
    ⟨hqS, Metric.mem_ball_self hr⟩, chartOpen_subset_of_chartDomain S hball, fun n w hw => ?_⟩
  have hc : d (chartDomain_isOpen S hU) (n + 1) (localRepresentative ρ S (n + 1) w) = 0 := by
    rw [← localRepresentative_d ρ S hU, hw, map_zero]
  obtain ⟨z, hz⟩ := hprim n (localRepresentative ρ S (n + 1) w) hc
  refine ⟨chartExtendOn ρ S Metric.isOpen_ball n z, ?_⟩
  rw [chartExtendOn_d, hz, chartExtendOn_localRepresentative ρ S Metric.isOpen_ball hball]

/-- Coefficient transition law for a section over an arbitrary quotient open set. The deck
transition comes from the actual covering charts and is locally constant on the overlap. -/
theorem localRepresentative_transition (S T : Space) (x : Coordinates)
    (hx : x ∈ ((quotientChart S).symm.trans (quotientChart T)).source)
    (hxU : (quotientChart S).symm x ∈ U) :
    ∃ g : DeckGroup,
      ((quotientChart S).symm.trans (quotientChart T)) =ᶠ[𝓝 x] deckMap g ∧
      ∀ (n : ℕ) (w : EquivariantForm ρ U n),
        pullRaw ((quotientChart S).symm.trans (quotientChart T))
          (localRepresentative ρ T n w : RawForm Coordinates F n) x =
        coefficientFormMap (coefficientMap ρ g) n
          ((localRepresentative ρ S n w : RawForm Coordinates F n) x) := by
  obtain ⟨g, hg⟩ := quotientChart_transition_eventually S T x hx
  change ((quotientChart S).symm.trans (quotientChart T)) =ᶠ[𝓝 x] deckMap g at hg
  refine ⟨g, hg, fun n w => ?_⟩
  have hs : x ∈ chartDomain S U := ⟨hx.1, hxU⟩
  have ht : deckMap g x ∈ chartDomain T U := by
    rw [← hg.self_of_nhds]
    refine ⟨(quotientChart T).map_source hx.2, ?_⟩
    change (quotientChart T).symm (quotientChart T ((quotientChart S).symm x)) ∈ U
    have hxt : (quotientChart S).symm x ∈ (quotientChart T).source := hx.2
    rw [(quotientChart T).left_inv hxt]
    exact hxU
  rw [pullRaw_eventuallyEq _ hg, localRepresentative_apply ρ S w hs]
  change ((localRepresentative ρ T n w : RawForm Coordinates F n) (deckMap g x)).compContinuousLinearMap _ = _
  rw [localRepresentative_apply ρ T w ht]
  exact w.property g x (chartDomain_liftedDomain S hs)

end TernaryPoly.SmoothCoveringDeRham
