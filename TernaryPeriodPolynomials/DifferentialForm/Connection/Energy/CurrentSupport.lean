module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDeck
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport

@[expose] public section


/-! The actual current of a compact quotient form has compact projected support. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham SmoothLocalDeRham Set
open scoped ContDiff

theorem energyCurrent_projected_support_subset (n k : ℕ)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    closure (coordinateProjection '' Function.support (energyCurrent n k w.val.val)) ⊆ quotientSupport w := by
  apply closure_mono
  apply image_mono
  intro x hx
  change w.val.val x ≠ 0
  intro hz
  exact hx (energyCurrent_of_eq_zero n k w.val.val x hz)

theorem energyCurrent_compact_projected_support (n k : ℕ)
    (w : CompactSupportForm (deckRepresentation n) univ k) :
    IsCompact (closure (coordinateProjection '' Function.support (energyCurrent n k w.val.val.val))) :=
  w.property.1.of_isClosed_subset isClosed_closure (energyCurrent_projected_support_subset n k w.val)

theorem energyCurrent_compact_smooth (n k : ℕ)
    (w : CompactSupportForm (deckRepresentation n) univ k) :
    ContDiffOn ℝ ∞ (energyCurrent n k w.val.val.val) positiveCoordinates := by
  apply contDiffOn_energyCurrent
  simpa only [liftedDomain_univ] using Form.smooth w.val.val

theorem energyCurrent_compact_outside (n k : ℕ)
    (w : CompactSupportForm (deckRepresentation n) univ k) (x : Coordinates)
    (hx : x ∉ positiveCoordinates) : energyCurrent n k w.val.val.val x = 0 := by
  apply energyCurrent_of_eq_zero
  exact Form.outside w.val.val (by simpa only [liftedDomain_univ] using hx)

end TernaryPoly.PolynomialFormConnection
