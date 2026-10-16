module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Pairing
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic
public import TernaryPeriodPolynomials.DifferentialForm.LocalIntegrationByParts

@[expose] public section


/-! Exact genuine Hilbert pairing in both zero-extended chart representatives. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham SmoothLocalDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceRiemannian
  PolynomialFormHilbert CompactCoordinateIntegration
open scoped SymmetricSpaceRiemannian

theorem inner_inclusion_chart (n k : ℕ) (S : Space) (a b : Core n k)
    (hs : quotientSupport a.val ⊆ (quotientChart S).source) :
    inner ℝ (inclusion n k a) (inclusion n k b) =
      ∫ x, weightedPairing (weightedGram n k)
        (components n k (globalChartRepresentative (deckRepresentation n) S k a.val).val)
        (components n k (globalChartRepresentative (deckRepresentation n) S k b.val).val) x := by
  apply (inner_inclusion n k a b).trans
  apply (integral_scalarPairing_chart n k S a b.val hs).trans
  unfold localIntegral
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  rw [weightedPairing_components]
  by_cases hx : x ∈ (quotientChart S).target
  · exact congrArg (fun z : FormValue n k => coordinateDensity x * formPairing n k x
      ((globalChartRepresentative (deckRepresentation n) S k a.val).val x) z)
      (globalChartRepresentative_apply (deckRepresentation n) S b.val hx).symm
  · have ha := Form.outside (globalChartRepresentative (deckRepresentation n) S k a.val) hx
    simp only [ha, formPairing_zero_left]

theorem weightedPairing_chart_symm (n k : ℕ) (S : Space)
    (a b : EquivariantForm (deckRepresentation n) univ k) (x : Coordinates) :
    weightedPairing (weightedGram n k)
      (components n k (globalChartRepresentative (deckRepresentation n) S k a).val)
      (components n k (globalChartRepresentative (deckRepresentation n) S k b).val) x =
    weightedPairing (weightedGram n k)
      (components n k (globalChartRepresentative (deckRepresentation n) S k b).val)
      (components n k (globalChartRepresentative (deckRepresentation n) S k a).val) x := by
  rw [weightedPairing_components, weightedPairing_components]
  by_cases hx : x ∈ (quotientChart S).target
  · rw [formPairing_symm n k x (quotientChart_target_subset S hx)]
  · have ha := Form.outside (globalChartRepresentative (deckRepresentation n) S k a) hx
    simp only [ha, formPairing_zero_left, formPairing_zero_right]

theorem inner_inclusion_chart_right (n k : ℕ) (S : Space) (a b : Core n k)
    (hs : quotientSupport b.val ⊆ (quotientChart S).source) :
    inner ℝ (inclusion n k a) (inclusion n k b) =
      ∫ x, weightedPairing (weightedGram n k)
        (components n k (globalChartRepresentative (deckRepresentation n) S k a.val).val)
        (components n k (globalChartRepresentative (deckRepresentation n) S k b.val).val) x := by
  apply (real_inner_comm (inclusion n k b) (inclusion n k a)).trans
  apply (inner_inclusion_chart n k S b a hs).trans
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (weightedPairing_chart_symm n k S b.val a.val)

end TernaryPoly.PolynomialFormCoordinates
