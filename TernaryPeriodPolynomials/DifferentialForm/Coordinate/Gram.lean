module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Basis

@[expose] public section


/-! Smoothness and invertibility of the genuine density-weighted form Gram matrix. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiffOn_weightedGram (n k : ℕ) :
    ContDiffOn ℝ ∞ (weightedGram n k) positiveCoordinates := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_coordinateDensity.mul (contDiffOn_formPairing n k _ _)

theorem weightedGram_isUnit (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    IsUnit (weightedGram n k x) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (weightedGram_posDef n k x hx).det_pos)

theorem contDiffOn_weightedGram_inverse (n k : ℕ) :
    ContDiffOn ℝ ∞ (fun x => (weightedGram n k x)⁻¹) positiveCoordinates :=
  contDiffOn_matrix_inverse (contDiffOn_weightedGram n k) (weightedGram_isUnit n k)

end TernaryPoly.PolynomialFormCoordinates
