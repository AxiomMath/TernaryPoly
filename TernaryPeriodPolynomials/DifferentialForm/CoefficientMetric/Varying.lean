module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Normalization
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.SmoothFischer
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricSpaceBundle

@[expose] public section


/-! The actual smooth admissible coefficient metric on the positive trace-one covering. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold
open scoped ContDiff Manifold Matrix.Norms.Elementwise

def coefficientMetric (n : ℕ) (S : Space) : Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ :=
  matrixContinuousBilin n (normalizedForm S)

@[simp] theorem coefficientMetric_apply (n : ℕ) (S : Space) (p q : Coefficients n) :
    coefficientMetric n S p q = matrixPairing (normalizedForm S) p.val q.val := rfl

theorem coefficientMetric_positive (n : ℕ) (S : Space) (p : Coefficients n) (hp : p ≠ 0) :
    0 < coefficientMetric n S p p :=
  matrixPairing_positive _ (determinantNormalize_positive S.val S.property.1) p.val
    (fun h => hp (Subtype.ext h))

theorem coefficientMetric_symmetric (n : ℕ) (S : Space) (p q : Coefficients n) :
    coefficientMetric n S p q = coefficientMetric n S q p := by
  apply matrixPairing_symmetric
  have h := (determinantNormalize_positive S.val S.property.1).isHermitian
  exact Matrix.isHermitian_iff_isSymm.mp h

theorem coefficientMetric_basepoint (n : ℕ) (p q : Coefficients n) :
    coefficientMetric n basepoint p q = factorialPairing p.val q.val := by
  rw [coefficientMetric_apply, normalizedForm_basepoint, matrixPairing, realSubstitute_one]
  rfl

theorem coefficientMetric_deck_invariant (n : ℕ) (g : DeckGroup) (S : Space) (p q : Coefficients n) :
    coefficientMetric n (g • S) (deckRepresentation n g p) (deckRepresentation n g q) =
      coefficientMetric n S p q := by
  simp only [coefficientMetric_apply, deckRepresentation_apply, normalizedForm_deck]
  exact matrixPairing_congruence (deckMatrix g) (normalizedForm S) p.val q.val

def coordinateCoefficientMetric (n : ℕ) (x : Coordinates) :
    Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ :=
  matrixContinuousBilin n (determinantNormalize (reconstruct x))

theorem contDiffOn_normalizedForm_coordinates : ContDiffOn ℝ ∞
    (fun x : Coordinates => determinantNormalize (reconstruct x)) positiveCoordinates := by
  have hd := SymmetricSpaceTraceMetric.contDiffOn_det (s := positiveCoordinates)
    contDiff_reconstruct.contDiffOn
  have hp := hd.rpow_const_of_ne (p := -(1/3 : ℝ)) (fun x (hx : x ∈ positiveCoordinates) => hx.det_pos.ne')
  exact hp.smul contDiff_reconstruct.contDiffOn

theorem contDiffOn_coordinateCoefficientMetric (n : ℕ) :
    ContDiffOn ℝ ∞ (coordinateCoefficientMetric n) positiveCoordinates :=
  (contDiff_matrixContinuousBilin n).comp_contDiffOn contDiffOn_normalizedForm_coordinates

theorem coefficientMetric_coordinates (n : ℕ) (S : Space) :
    coordinateCoefficientMetric n (coordinateChart S) = coefficientMetric n S := by
  change matrixContinuousBilin n (determinantNormalize (reconstruct (extract S.val))) = _
  rw [reconstruct_extract S.val (Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian) S.property.2]
  rfl

theorem contMDiff_coefficientMetric (n : ℕ) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) ∞
      (coefficientMetric n) := by
  have h : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) ∞
      (fun S : Space => coordinateCoefficientMetric n (coordinateChart S)) := by
    rw [← contMDiffOn_univ]
    exact (contDiffOn_coordinateCoefficientMetric n).contMDiffOn.comp
      coordinateChart_contMDiff.contMDiffOn (fun S _ => extract_mem S)
  simpa only [coefficientMetric_coordinates] using h

end TernaryPoly.PolynomialCoefficientMetric
