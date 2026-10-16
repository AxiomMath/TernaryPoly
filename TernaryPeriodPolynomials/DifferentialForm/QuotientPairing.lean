module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Support
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.VolumePositive

@[expose] public section


/-! The genuine quotient metric integral, linear in a compact first form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian

theorem integrable_scalarPairing (n k : ℕ)
    (f : CompactSupportForm (deckRepresentation n) univ k)
    (g : EquivariantForm (deckRepresentation n) univ k) :
    Integrable (scalarPairing n k f.val g) orbitVolume :=
  (continuous_scalarPairing n k f.val g).integrable_of_hasCompactSupport
    (hasCompactSupport_scalarPairing n k f.val g f.property.1)

/-- The actual metric-volume integral on compact forms, with an arbitrary smooth second form. -/
def quotientPairingFunctional (n k : ℕ) (g : EquivariantForm (deckRepresentation n) univ k) :
    CompactSupportForm (deckRepresentation n) univ k →ₗ[ℝ] ℝ where
  toFun f := ∫ q, scalarPairing n k f.val g q ∂orbitVolume
  map_add' f z := by
    change (∫ q, scalarPairing n k (f.val + z.val) g q ∂orbitVolume) = _
    rw [scalarPairing_add_left]
    exact integral_add (integrable_scalarPairing n k f g) (integrable_scalarPairing n k z g)
  map_smul' c f := by
    change (∫ q, scalarPairing n k (c • f.val) g q ∂orbitVolume) = _
    rw [scalarPairing_smul_left]
    exact integral_smul c _

end TernaryPoly.PolynomialFormCoordinates
