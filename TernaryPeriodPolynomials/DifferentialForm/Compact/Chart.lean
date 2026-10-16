module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Representation
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Transitions
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section

/-! True compact support for the actual coordinate representative of a chart-supported quotient form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold SmoothCoveringDeRham SmoothLocalDeRham CompactCoordinateIntegration
open Set
open scoped ContDiff

/-- A form compactly supported inside one quotient chart has compact coordinate support inside its target. -/
theorem tsupport_globalChartRepresentative (n k : ℕ) (S : Space)
    (w : CompactSupportForm (deckRepresentation n) univ k)
    (hs : quotientSupport w.val ⊆ (quotientChart S).source) :
    tsupport (globalChartRepresentative (deckRepresentation n) S k w.val).val ⊆
      (quotientChart S) '' quotientSupport w.val := by
  have hK := w.property.1.image_of_continuousOn ((quotientChart S).continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hxt : x ∈ (quotientChart S).target := by
    by_contra hn
    exact hx (Form.outside (globalChartRepresentative (deckRepresentation n) S k w.val) hn)
  have hn : w.val.val.val x ≠ 0 := by
    change (globalChartRepresentative (deckRepresentation n) S k w.val).val x ≠ 0 at hx
    rwa [globalChartRepresentative_apply (deckRepresentation n) S w.val hxt] at hx
  refine ⟨coordinateProjection x, subset_closure ⟨x, hn, rfl⟩, ?_⟩
  rw [← quotientChart_projection_coordinates S hxt, (quotientChart S).right_inv hxt]

theorem hasCompactSupport_globalChartRepresentative (n k : ℕ) (S : Space)
    (w : CompactSupportForm (deckRepresentation n) univ k)
    (hs : quotientSupport w.val ⊆ (quotientChart S).source) :
    HasCompactSupport (globalChartRepresentative (deckRepresentation n) S k w.val).val :=
  (w.property.1.image_of_continuousOn ((quotientChart S).continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_globalChartRepresentative n k S w hs)

theorem tsupport_globalChartRepresentative_target (n k : ℕ) (S : Space)
    (w : CompactSupportForm (deckRepresentation n) univ k)
    (hs : quotientSupport w.val ⊆ (quotientChart S).source) :
    tsupport (globalChartRepresentative (deckRepresentation n) S k w.val).val ⊆
      (quotientChart S).target := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := tsupport_globalChartRepresentative n k S w hs hx
  exact (quotientChart S).map_source (hs hq)

/-- The actual zero-extended chart representative is globally smooth in Euclidean coordinates. -/
theorem contDiff_globalChartRepresentative (n k : ℕ) (S : Space)
    (w : CompactSupportForm (deckRepresentation n) univ k)
    (hs : quotientSupport w.val ⊆ (quotientChart S).source) :
    ContDiff ℝ ∞ (globalChartRepresentative (deckRepresentation n) S k w.val).val :=
  contDiff_of_tsupport_subset (quotientChart S).open_target
    (Form.smooth (globalChartRepresentative (deckRepresentation n) S k w.val))
    (tsupport_globalChartRepresentative_target n k S w hs)

end TernaryPoly.PolynomialFormCoordinates
