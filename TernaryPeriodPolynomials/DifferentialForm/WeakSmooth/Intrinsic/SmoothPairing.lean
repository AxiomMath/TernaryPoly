module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.LocalTest
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic

@[expose] public section


/-! Actual local smooth form pairings with intrinsic compact quotient tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormHilbert
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian SmoothCoveringDeRham
open scoped SymmetricSpaceRiemannian

/-- The genuine local metric pairing of a smooth local form with an actual intrinsic compact test. -/
def intrinsicSmoothPairing (n k : ℕ) (U : Set OrbitSpace)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) : OrbitSpace → ℝ :=
  scalarPairing n k a (supportedLocalTest n k U w).val

/-- Pairing with a genuine local compact test cannot enlarge its true quotient support. -/
theorem intrinsicSmoothPairing_tsupport (n k : ℕ) (U : Set OrbitSpace)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) :
    tsupport (intrinsicSmoothPairing n k U a w) ⊆ quotientSupport w.val.val := by
  intro q hq
  have h := (tsupport_scalarPairing n k a (supportedLocalTest n k U w).val hq).2
  exact (supportedCompactCore_restrict_support n k U w) ▸ h

/-- The genuine local pairing with an intrinsic compact test is globally continuous by its
actual support inside the local open set. -/
theorem intrinsicSmoothPairing_continuous (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) :
    Continuous (intrinsicSmoothPairing n k U a w) :=
  (contMDiffOn_scalarPairing n k hU a (supportedLocalTest n k U w).val).continuousOn.continuous_of_tsupport_subset
    hU ((intrinsicSmoothPairing_tsupport n k U a w).trans w.property)

/-- The literal quotient metric pairing of a local smooth form with an intrinsic compact test
is integrable for the actual quotient Riemannian measure. -/
theorem intrinsicSmoothPairing_integrable (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) :
    Integrable (intrinsicSmoothPairing n k U a w) orbitVolume :=
  (intrinsicSmoothPairing_continuous n k U hU a w).integrable_of_hasCompactSupport
    (w.val.property.1.of_isClosed_subset (isClosed_tsupport _) (intrinsicSmoothPairing_tsupport n k U a w))

end TernaryPoly.PolynomialFormWeakSmooth
