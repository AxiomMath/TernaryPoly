module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.ChainMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace}

/-- A locally constant coefficient section, extended by the true sheet action, is closed. -/
theorem constant_extension_closed (S : Space) {V : Set Coordinates} (hV : IsOpen V)
    (hc : IsPreconnected V) (c : F) :
    differential ρ (chartOpen_isOpen S hV) 0
      (chartExtendOn ρ S hV 0 (constant V c)) = 0 := by
  rw [chartExtendOn_d, (closed_zero_iff_constant hV hc (constant V c)).mpr ⟨c, rfl⟩, map_zero]

/-- The degree-zero kernel is the actual coefficient local system: near every quotient point,
a closed section is the sheet-equivariant extension of a constant coefficient value. -/
theorem closed_zero_local_constant (hU : IsOpen U) {q : OrbitSpace} (hq : q ∈ U)
    (w : EquivariantForm ρ U 0) (hw : differential ρ hU 0 w = 0) :
    ∃ S : Space, ∃ r : ℝ, 0 < r ∧
      ∃ hball : Metric.ball (quotientChart S q) r ⊆ chartDomain S U,
        q ∈ chartOpen S (Metric.ball (quotientChart S q) r) ∧ ∃ c : F,
          restrictEquivariant ρ (chartOpen_subset_of_chartDomain S hball) 0 w =
            chartExtendOn ρ S Metric.isOpen_ball 0 (constant (Metric.ball (quotientChart S q) r) c) := by
  obtain ⟨S, hqS⟩ := quotientCharts_cover q
  have hx : quotientChart S q ∈ chartDomain S U :=
    ⟨(quotientChart S).map_source hqS, by simpa only [mem_preimage, (quotientChart S).left_inv hqS] using hq⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (chartDomain_isOpen S hU) _ hx
  have hc : d Metric.isOpen_ball 0 (restrictTo hball 0 (localRepresentative ρ S 0 w)) = 0 := by
    rw [← restrictTo_d (chartDomain_isOpen S hU) Metric.isOpen_ball hball,
      ← localRepresentative_d ρ S hU, hw, map_zero, map_zero]
  obtain ⟨c, he⟩ := (closed_zero_iff_constant Metric.isOpen_ball
    (convex_ball (quotientChart S q) r).isPreconnected _).mp hc
  refine ⟨S, r, hr, hball, ⟨hqS, Metric.mem_ball_self hr⟩, c, ?_⟩
  rw [← chartExtendOn_localRepresentative ρ S Metric.isOpen_ball hball, he]

end TernaryPoly.SmoothCoveringDeRham
