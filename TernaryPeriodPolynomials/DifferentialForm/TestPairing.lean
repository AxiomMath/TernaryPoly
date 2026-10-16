module

public import TernaryPeriodPolynomials.DifferentialForm.TestUniqueness
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section


/-! Integrability and pointwise uniqueness for the genuine local form pairing. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian CompactCoordinateIntegration
open Set MeasureTheory
open scoped ContDiff

/-- The density-weighted scalar pairing is supported in the first form's closed support. -/
theorem tsupport_densityPairing (n k : ℕ) (f g : Coordinates → FormValue n k) :
    tsupport (fun x => coordinateDensity x * formPairing n k x (f x) (g x)) ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [hx, formPairing_zero_left, mul_zero]

/-- A compact first form gives a genuine integrable local metric pairing. -/
theorem integrable_densityPairing (n k : ℕ) {f g : Coordinates → FormValue n k}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) (hg : ContDiffOn ℝ ∞ g positiveCoordinates)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ positiveCoordinates) :
    Integrable (fun x => coordinateDensity x * formPairing n k x (f x) (g x)) := by
  have ht := tsupport_densityPairing n k f g
  have hd := contDiff_of_tsupport_subset isOpen_positiveCoordinates
    (contDiffOn_coordinateDensity.mul (contDiffOn_formPairing_functions n k Subset.rfl hf hg))
    (ht.trans hs)
  exact hd.continuous.integrable_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) ht)

/-- Equality of all actual compact test pairings determines the smooth form everywhere. -/
theorem eqOn_of_form_test_integrals (n k : ℕ) {g z : Coordinates → FormValue n k}
    (hg : ContDiffOn ℝ ∞ g positiveCoordinates) (hz : ContDiffOn ℝ ∞ z positiveCoordinates)
    (h : ∀ f : Coordinates → FormValue n k, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ positiveCoordinates →
      ∫ x, coordinateDensity x * formPairing n k x (f x) (g x) =
        ∫ x, coordinateDensity x * formPairing n k x (f x) (z x)) :
    EqOn g z positiveCoordinates := by
  have he : EqOn (fun x => g x - z x) 0 positiveCoordinates := by
    apply eqOn_zero_of_form_test_integrals n k (hg.sub hz)
    intro f hf hc hs
    have hp (x : Coordinates) : formPairing n k x (f x) (g x - z x) =
        formPairing n k x (f x) (g x) - formPairing n k x (f x) (z x) :=
      (formBilinear n k x (f x)).map_sub (g x) (z x)
    simp only [hp, mul_sub]
    rw [integral_sub (integrable_densityPairing n k hf.contDiffOn hg hc hs)
      (integrable_densityPairing n k hf.contDiffOn hz hc hs), h f hf hc hs, sub_self]
  intro x hx
  exact sub_eq_zero.mp (he hx)

end TernaryPoly.PolynomialFormCoordinates
