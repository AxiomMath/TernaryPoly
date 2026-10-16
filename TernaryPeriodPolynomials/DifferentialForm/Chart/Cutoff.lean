module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.Chart
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Differential

@[expose] public section



/-! A genuine inner chart cutoff, defined on every actual global smooth quotient form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold CompactCoordinateIntegration
open scoped ContDiff

def cutoffChartRaw (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) : Coordinates → FormValue n k :=
  fun x => χ x • (globalChartRepresentative (deckRepresentation n) S k w).val x

theorem tsupport_cutoffChartRaw (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    tsupport (cutoffChartRaw n k S χ w) ⊆ tsupport χ :=
  tsupport_smul_subset_left χ (globalChartRepresentative (deckRepresentation n) S k w).val

theorem contDiff_cutoffChartRaw (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    ContDiff ℝ ∞ (cutoffChartRaw n k S χ w) :=
  contDiff_of_tsupport_subset (quotientChart S).open_target
    (hχ.contDiffOn.smul (Form.smooth (globalChartRepresentative (deckRepresentation n) S k w)))
    ((tsupport_cutoffChartRaw n k S χ w).trans hs)

theorem compact_cutoffChartRaw (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hc : HasCompactSupport χ) (w : EquivariantForm (deckRepresentation n) univ k) :
    HasCompactSupport (cutoffChartRaw n k S χ w) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_cutoffChartRaw n k S χ w)

/-- Scalar coordinates inherit genuine global smoothness from the compact chart cutoff. -/
theorem contDiff_cutoffChartComponents (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    ContDiff ℝ ∞ (components n k (cutoffChartRaw n k S χ w) i) :=
  by
    have hcoord : ContDiff ℝ ∞ (coordinates n k) :=
      ContinuousLinearEquiv.contDiff (𝕜 := ℝ) (E := FormValue n k) (F := Index n k → ℝ) (coordinates n k)
    have h : ContDiff ℝ ∞ (fun x => coordinates n k (cutoffChartRaw n k S χ w x)) :=
      ContDiff.comp (𝕜 := ℝ) (E := Coordinates) (F := FormValue n k)
        (G := Index n k → ℝ) hcoord (contDiff_cutoffChartRaw n k S χ hχ hs w)
    exact contDiff_pi.mp h i

theorem compact_cutoffChartComponents (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hc : HasCompactSupport χ) (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    HasCompactSupport (components n k (cutoffChartRaw n k S χ w) i) := by
  apply (compact_cutoffChartRaw n k S χ hc w).of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  change coordinates n k (cutoffChartRaw n k S χ w x) i = 0
  rw [hx, ContinuousLinearEquiv.map_zero]
  rfl

end TernaryPoly.PolynomialFormCoordinates
