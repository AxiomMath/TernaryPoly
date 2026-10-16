module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.HilbertNorm
public import TernaryPeriodPolynomials.DifferentialForm.WeightedCoordinateUpper

@[expose] public section


/-! Uniform coordinate control of the actual Hilbert norm for forms supported in one compact chart set. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

theorem quotientSupport_source_of_chart_image (n k : ℕ) (S : Space) (K : Set Coordinates)
    (hK : K ⊆ (quotientChart S).target) (w : Core n k)
    (hw : quotientSupport w.val ⊆ (quotientChart S).symm '' K) :
    quotientSupport w.val ⊆ (quotientChart S).source := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := hw hq
  exact (quotientChart S).map_target (hK hx)

theorem tsupport_globalChartRepresentative_of_chart_image (n k : ℕ) (S : Space) (K : Set Coordinates)
    (hK : K ⊆ (quotientChart S).target) (w : Core n k)
    (hw : quotientSupport w.val ⊆ (quotientChart S).symm '' K) :
    tsupport (globalChartRepresentative (deckRepresentation n) S k w.val).val ⊆ K := by
  intro x hx
  have hs := quotientSupport_source_of_chart_image n k S K hK w hw
  obtain ⟨q,hq,rfl⟩ := tsupport_globalChartRepresentative n k S w hs hx
  obtain ⟨y,hy,rfl⟩ := hw hq
  simpa only [(quotientChart S).right_inv (hK hy)] using hy

theorem exists_chart_supported_norm_bound (n k : ℕ) (S : Space) (K : Set Coordinates)
    (hcK : IsCompact K) (hsK : K ⊆ (quotientChart S).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Core n k, quotientSupport w.val ⊆ (quotientChart S).symm '' K →
      ‖inclusion n k w‖^2 ≤ C * ∑ i, ∫ x,
        ‖components n k (globalChartRepresentative (deckRepresentation n) S k w.val).val i x‖^2 := by
  have H := exists_compact_weighted_coordinate_upper n k hcK
    (hsK.trans (quotientChart_target_subset S))
  let C : ℝ := H.choose
  refine ⟨C,H.choose_spec.1,fun w hw => ?_⟩
  have hs := quotientSupport_source_of_chart_image n k S K hsK w hw
  have ht := tsupport_globalChartRepresentative_of_chart_image n k S K hsK w hw
  exact (norm_inclusion_square_chart n k S w hs).le.trans
    (H.choose_spec.2 _ (contDiff_globalChartRepresentative n k S w hs)
      (hasCompactSupport_globalChartRepresentative n k S w hs) ht)

end TernaryPoly.PolynomialFormCoordinates
