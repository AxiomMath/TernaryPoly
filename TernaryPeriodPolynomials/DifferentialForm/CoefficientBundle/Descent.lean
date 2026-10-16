module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Topology
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Metric

@[expose] public section


/-! The quotient projection and literal descent identity for the coefficient metric. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
open Bundle

def associatedProjection (n : ℕ) (z : Associated n) : OrbitSpace := (associatedHomeomorph n z).proj

@[simp] theorem associatedProjection_class (n : ℕ) (S : Space) (p : Coefficients n) :
    associatedProjection n (orbitClass n S p) = quotientProjection S := rfl

@[simp] theorem associatedHomeomorph_projection (n : ℕ) (z : Associated n) :
    (associatedHomeomorph n z).proj = associatedProjection n z := rfl

/-- The metric in the glued bundle pulls back to the metric on the
literal covering product, at every base point and for every pair of coefficient vectors. -/
theorem fiberMetric_descent (n : ℕ) (S : Space) (p q : Coefficients n) :
    fiberMetric n (quotientProjection S) (liftToTotal n (S,p)).snd (liftToTotal n (S,q)).snd =
      coefficientMetric n S p q := by
  change coefficientMetric n (chosenLift (quotientProjection S))
    (coefficientAction n (deckBetween S (chosenLift (quotientProjection S))) p)
    (coefficientAction n (deckBetween S (chosenLift (quotientProjection S))) q) = _
  have h := coefficientMetric_deck_invariant n (deckBetween S (chosenLift (quotientProjection S))) S p q
  rw [deckBetween_spec S _ (chosenLift_projection _)] at h
  exact h

/-- The quotient class of a rational coefficient respects every integer twist through the
literal rational-to-real coefficient inclusion. -/
theorem rational_orbitClass_equivariant (n : ℕ) (e : ℤ) (g : DeckGroup) (S : Space)
    (p : RationalCoefficients n) :
    orbitClass n (g • S) (scalarExtensionCoefficient n (rationalDeckRepresentation n e g p)) =
      orbitClass n S (scalarExtensionCoefficient n p) := by
  rw [scalarExtensionCoefficient_equivariant]
  exact orbitClass_smul n g S _

end TernaryPoly.PolynomialCoefficientBundle
