module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Pairing
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic

@[expose] public section


/-! The literal Hilbert norm of an actual chart-supported quotient form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  SymmetricSpaceRiemannian PolynomialFormHilbert

theorem norm_inclusion_square_chart (n k : ℕ) (S : Space) (w : Core n k)
    (hs : quotientSupport w.val ⊆ (quotientChart S).source) :
    ‖inclusion n k w‖ ^ 2 = ∫ x, coordinateDensity x * formPairing n k x
      ((globalChartRepresentative (deckRepresentation n) S k w.val).val x)
      ((globalChartRepresentative (deckRepresentation n) S k w.val).val x) := by
  have hnorm : ‖inclusion n k w‖^2 = ∫ q, scalarPairing n k w.val w.val q ∂orbitVolume :=
    (real_inner_self_eq_norm_sq (inclusion n k w)).symm.trans (inner_inclusion n k w w)
  refine hnorm.trans ((integral_scalarPairing_chart n k S w w.val hs).trans ?_)
  unfold localIntegral
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : x ∈ (quotientChart S).target
  · exact congrArg (fun a : FormValue n k => coordinateDensity x * formPairing n k x
      ((globalChartRepresentative (deckRepresentation n) S k w.val).val x) a)
      (globalChartRepresentative_apply (deckRepresentation n) S w.val hx).symm
  · have h0 := Form.outside (globalChartRepresentative (deckRepresentation n) S k w.val) hx
    simp only [h0, formPairing_zero_left]

end TernaryPoly.PolynomialFormCoordinates
