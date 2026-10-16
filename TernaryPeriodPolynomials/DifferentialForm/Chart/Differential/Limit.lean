module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.Limit

@[expose] public section

/-! The actual compact-form limit of the exterior differential chart commutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target)

def coreChartDifferentialLimit (w : Core n k) : Core n (k+1) :=
  compactDifferential (deckRepresentation n) isOpen_univ k
    (doubleChartCutoff n k S χ η hχ hη hcη hsη w.val) -
      doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη
        (compactDifferential (deckRepresentation n) isOpen_univ k w).val

theorem quotientSupport_coreChartDifferentialLimit (w : Core n k) :
    quotientSupport (coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w).val ⊆
      (quotientChart S).symm '' tsupport η :=
  (quotientSupport_sub _ _).trans (union_subset
    ((quotientSupport_differential isOpen_univ _).trans
      (quotientSupport_doubleChartCutoff n k S χ η hχ hη hcη hsη w.val))
    (quotientSupport_doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη
      (compactDifferential (deckRepresentation n) isOpen_univ k w).val))

theorem globalChartRepresentative_coreChartDifferentialLimit (w : Core n k) :
    (globalChartRepresentative (deckRepresentation n) S (k+1)
      (coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w).val).val =
      extDeriv (fun x => η x • cutoffChartRaw n k S χ w.val x) -
        (fun x => η x • cutoffChartRaw n (k+1) S χ
          (compactDifferential (deckRepresentation n) isOpen_univ k w).val x) := by
  let a := doubleChartCutoff n k S χ η hχ hη hcη hsη w.val
  have hs := quotientSupport_chartCutoff n k S (η*χ) (hη.mul hχ) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη) w.val
  have hD := (globalChartRepresentative_compactDifferential n k S a hs).trans
    (congrArg extDeriv (globalChartRepresentative_doubleChartCutoff n k S χ η hχ hη hcη hsη w.val))
  have hR := globalChartRepresentative_doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη
    (compactDifferential (deckRepresentation n) isOpen_univ k w).val
  exact (globalChartRepresentative_sub n (k+1) S _ _).trans
    (congrArg₂ (fun u v : Coordinates → FormValue n (k+1) => u-v) hD hR)

end TernaryPoly.PolynomialFormCoordinates
