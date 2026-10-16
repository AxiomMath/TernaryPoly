module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Infinitesimal
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Tensor

@[expose] public section


/-! Smooth positive admissible metrics for the literal polynomial deck representation.
This package does not assert any associated-bundle de Rham or global Laplacian comparison. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Manifold Matrix.Norms.Elementwise

theorem coefficientMetric_frame (n : ℕ) (S : Space) (g : Mat)
    (hg : normalizedForm S = g * g.transpose) (p q : Coefficients n) :
    coefficientMetric n S p q = factorialPairing (realSubstitute g p.val) (realSubstitute g q.val) := by
  rw [coefficientMetric_apply, hg, matrixPairing_frame]

theorem coefficientMetric_frame_independent (n : ℕ) (S : Space) (g h : Mat)
    (hg : normalizedForm S = g * g.transpose) (hh : normalizedForm S = h * h.transpose)
    (p q : Coefficients n) :
    factorialPairing (realSubstitute g p.val) (realSubstitute g q.val) =
      factorialPairing (realSubstitute h p.val) (realSubstitute h q.val) := by
  rw [← coefficientMetric_frame n S g hg, ← coefficientMetric_frame n S h hh]

theorem coefficientMetric_admissible (n : ℕ) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) ∞
      (coefficientMetric n) ∧
    (∀ S (p q : Coefficients n), coefficientMetric n S p q = coefficientMetric n S q p) ∧
    (∀ S (p : Coefficients n), p ≠ 0 → 0 < coefficientMetric n S p p) ∧
    (∀ (g : DeckGroup) S (p q : Coefficients n),
      coefficientMetric n (g • S) (deckRepresentation n g p) (deckRepresentation n g q) =
        coefficientMetric n S p q) ∧
    (∀ p q : Coefficients n, coefficientMetric n basepoint p q = factorialPairing p.val q.val) :=
  ⟨contMDiff_coefficientMetric n, coefficientMetric_symmetric n, coefficientMetric_positive n,
    coefficientMetric_deck_invariant n, coefficientMetric_basepoint n⟩

end TernaryPoly.PolynomialCoefficientMetric
