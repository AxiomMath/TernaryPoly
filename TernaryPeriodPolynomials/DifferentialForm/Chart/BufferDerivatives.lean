module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Buffer
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Adjoint

@[expose] public section


/-! Input localization of the true differential and codifferential is unchanged by a chart buffer. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff Topology

theorem cutoffChartRaw_differential_buffer (n k : ℕ) (S : Space) (χ θ : Coordinates → ℝ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hθ : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (w : CompactSupportForm (deckRepresentation n) univ k) :
    cutoffChartRaw n (k+1) S χ (compactDifferential (deckRepresentation n) isOpen_univ k w).val =
      fun x => χ x • extDeriv (cutoffChartRaw n k S θ w.val) x := by
  funext x
  by_cases hx : x ∈ tsupport χ
  · have hxt := hsχ hx
    have he := cutoffChartRaw_eventuallyEq n k S θ w.val hxt (hθ x hx)
    change χ x • (globalChartRepresentative (deckRepresentation n) S (k+1)
      (compactDifferential (deckRepresentation n) isOpen_univ k w).val).val x = _
    rw [globalChartRepresentative_apply (deckRepresentation n) S _ hxt]
    have hd := d_apply (liftedDomain_isOpen isOpen_univ) w.val.val
      (by simpa only [liftedDomain_univ] using quotientChart_target_subset S hxt)
    exact congrArg (χ x • ·) (hd.trans he.extDeriv_eq.symm)
  · exact smul_eq_smul_of_zero (F := FormValue n (k+1)) (image_eq_zero_of_notMem_tsupport hx) _ _

theorem cutoffChartRaw_adjoint_buffer (n k : ℕ) (S : Space) (χ θ : Coordinates → ℝ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hθ : ∀ x ∈ tsupport χ, θ =ᶠ[𝓝 x] 1)
    (w : CompactSupportForm (deckRepresentation n) univ (k+1)) :
    cutoffChartRaw n k S χ (compactAdjoint n k w).val =
      fun x => χ x • localAdjoint n k (cutoffChartRaw n (k+1) S θ w.val) x := by
  funext x
  by_cases hx : x ∈ tsupport χ
  · have hxt := hsχ hx
    have he := cutoffChartRaw_eventuallyEq n (k+1) S θ w.val hxt (hθ x hx)
    change χ x • (globalChartRepresentative (deckRepresentation n) S k (compactAdjoint n k w).val).val x = _
    rw [globalChartRepresentative_apply (deckRepresentation n) S _ hxt]
    exact congrArg (χ x • ·) ((compactAdjoint_apply n k w (quotientChart_target_subset S hxt)).trans
      (localAdjoint_congr n k he).symm)
  · exact smul_eq_smul_of_zero (F := FormValue n k) (image_eq_zero_of_notMem_tsupport hx) _ _

end TernaryPoly.PolynomialFormCoordinates
