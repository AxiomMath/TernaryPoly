module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothRestriction
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Chart
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.ChartIntegral

@[expose] public section


/-! Genuine quotient integral of a local smooth form against a chart-supported intrinsic test. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormCoordinates
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SymmetricSpaceRiemannian
  SmoothCoveringDeRham SmoothLocalDeRham
open scoped SymmetricSpaceRiemannian

/-- The genuine quotient pairing with an actual chart-supported test has its literal coordinate
density integral, for arbitrary genuine local smooth coefficient forms. -/
theorem intrinsicSmoothPairing_integral_chart (n k : ℕ) (U : Set OrbitSpace)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U)
    (S : Space) (hs : quotientSupport w.val.val ⊆ (quotientChart S).source) :
    (∫ q, intrinsicSmoothPairing n k U a w q ∂orbitVolume) =
      ∫ x, coordinateDensity x * formPairing n k x (a.val.val x)
        ((globalChartRepresentative (deckRepresentation n) S k w.val.val).val x) := by
  have hsupport : Function.support (intrinsicSmoothPairing n k U a w) ⊆ (quotientChart S).source :=
    (subset_tsupport _).trans ((intrinsicSmoothPairing_tsupport n k U a w).trans hs)
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := (quotientChart S).source)
    (fun q hq => by by_contra hn; exact hq (hsupport hn))).symm.trans
  apply (orbitVolume_integral_chart S (intrinsicSmoothPairing n k U a w)).trans
  apply Eq.trans _ (setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := (quotientChart S).target)
    (f := fun x => coordinateDensity x * formPairing n k x (a.val.val x)
      ((globalChartRepresentative (deckRepresentation n) S k w.val.val).val x))
    (fun x hx => by rw [Form.outside _ hx, formPairing_zero_right, mul_zero]))
  apply setIntegral_congr_fun (quotientChart S).open_target.measurableSet
  intro x hx
  apply congrArg (coordinateDensity x * ·)
  exact (congrArg (intrinsicSmoothPairing n k U a w) (quotientChart_projection_coordinates S hx)).trans
    ((intrinsicSmoothPairing_coordinateProjection n k U a w x (quotientChart_target_subset S hx)).trans
      (congrArg (formPairing n k x (a.val.val x))
        (globalChartRepresentative_apply (deckRepresentation n) S w.val.val hx).symm))

end TernaryPoly.PolynomialFormWeakSmooth
