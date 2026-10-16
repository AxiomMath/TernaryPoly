module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.Chart
public import TernaryPeriodPolynomials.DifferentialForm.Metric.Support
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.ChartIntegral
public import TernaryPeriodPolynomials.DifferentialForm.Deck.Integration

@[expose] public section


/-! Exact coordinate expression for a chart-supported genuine quotient form pairing. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold SymmetricSpaceRiemannian SmoothCoveringDeRham SmoothLocalDeRham
open Set MeasureTheory
open scoped SymmetricSpaceRiemannian

/-- A quotient form pairing supported inside one chart has the literal coordinate-density integral. -/
theorem integral_scalarPairing_chart (n k : ℕ) (S : Space)
    (f : CompactSupportForm (deckRepresentation n) univ k)
    (g : EquivariantForm (deckRepresentation n) univ k)
    (hs : quotientSupport f.val ⊆ (quotientChart S).source) :
    ∫ q, scalarPairing n k f.val g q ∂orbitVolume =
      localIntegral n k (globalChartRepresentative (deckRepresentation n) S k f.val).val g.val.val := by
  have hsupport : Function.support (scalarPairing n k f.val g) ⊆ (quotientChart S).source := by
    intro q hq
    exact hs (subset_closure (support_scalarPairing n k f.val g hq).1)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (quotientChart S).source)
    (fun q hq => by by_contra hn; exact hq (hsupport hn)), orbitVolume_integral_chart]
  have hrep0 (x : Coordinates) (hx : x ∉ (quotientChart S).target) :
      (globalChartRepresentative (deckRepresentation n) S k f.val).val x = 0 :=
    Form.outside _ hx
  unfold localIntegral
  refine Eq.trans ?_ (setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := (quotientChart S).target)
    (f := fun x => coordinateDensity x * formPairing n k x
      ((globalChartRepresentative (deckRepresentation n) S k f.val).val x) (g.val.val x))
    (fun x hx => by rw [hrep0 x hx, formPairing_zero_left, mul_zero]))
  apply setIntegral_congr_fun (quotientChart S).open_target.measurableSet
  intro x hx
  dsimp only
  apply congrArg (coordinateDensity x * ·)
  calc
    _ = scalarPairing n k f.val g (coordinateProjection x) :=
      congrArg (scalarPairing n k f.val g) (quotientChart_projection_coordinates S hx)
    _ = formPairing n k x (f.val.val.val x) (g.val.val x) :=
      scalarPairing_coordinateProjection n k f.val g x (quotientChart_target_subset S hx)
    _ = _ := congrArg (fun v => formPairing n k x v (g.val.val x))
      (globalChartRepresentative_apply (deckRepresentation n) S f.val hx).symm


end TernaryPoly.PolynomialFormCoordinates
