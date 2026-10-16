module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Cutoff
public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCutoff
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Locality

@[expose] public section


/-! Smooth chart buffers preserve genuine form germs near the active cutoff supports. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff Topology

theorem smul_eq_smul_of_zero {F : Type*} [AddCommGroup F] [Module ℝ F]
    {c : ℝ} (hc : c = 0) (a b : F) : c • a = c • b := by
  rw [hc, zero_smul, zero_smul]

theorem exists_chart_buffer (S : Space) (χ η : Coordinates → ℝ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target) :
    ∃ θ : Coordinates → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ (quotientChart S).target ∧
      ∀ x ∈ tsupport χ ∪ tsupport η, θ =ᶠ[𝓝 x] 1 := by
  exact CompactSmoothCutoff.exists_cutoff (hcχ.union hcη) (quotientChart S).open_target
    (union_subset hsχ hsη)

theorem cutoffChartRaw_eventuallyEq (n k : ℕ) (S : Space) (θ : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) {x : Coordinates}
    (hx : x ∈ (quotientChart S).target) (hθ : θ =ᶠ[𝓝 x] 1) :
    cutoffChartRaw n k S θ w =ᶠ[𝓝 x] w.val.val := by
  filter_upwards [hθ,(quotientChart S).open_target.mem_nhds hx] with y hy hyt
  change θ y • (globalChartRepresentative (deckRepresentation n) S k w).val y = _
  rw [hy, Pi.one_apply, one_smul, globalChartRepresentative_apply (deckRepresentation n) S w hyt]

theorem cutoffChartRaw_buffer (n k : ℕ) (S : Space) (χ θ : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k)
    (hθ : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1) :
    cutoffChartRaw n k S χ w = fun x => χ x • cutoffChartRaw n k S θ w x := by
  funext x
  by_cases hx : x ∈ tsupport χ
  · have he : θ x = 1 := (hθ x hx).self_of_nhds
    simp only [cutoffChartRaw, he, one_smul]
  · change χ x • _ = χ x • _
    rw [image_eq_zero_of_notMem_tsupport hx]
    exact (zero_smul ℝ ((globalChartRepresentative (deckRepresentation n) S k w).val x)).trans
      (zero_smul ℝ (cutoffChartRaw n k S θ w x)).symm

end TernaryPoly.PolynomialFormCoordinates
