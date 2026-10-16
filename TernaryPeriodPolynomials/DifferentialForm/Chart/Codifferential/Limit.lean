module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.StrongConvergence
public import TernaryPeriodPolynomials.DifferentialForm.Chart.CommutatorRepresentative

@[expose] public section


/-! The actual compact-form candidate limit of the codifferential chart commutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

theorem quotientSupport_chartCutoff_image (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    quotientSupport (chartCutoff n k S χ hχ hcχ hsχ w).val ⊆ (quotientChart S).symm '' tsupport χ :=
  (quotientSupport_compactChartExtend (deckRepresentation n) S (cutoffChartForm n k S χ hχ hsχ w)
    (compact_cutoffChartRaw n k S χ hcχ w) ((tsupport_cutoffChartRaw n k S χ w).trans hsχ)).trans
    (image_mono (tsupport_cutoffChartRaw n k S χ w))

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target)

theorem globalChartRepresentative_doubleChartCutoff (w : EquivariantForm (deckRepresentation n) univ k) :
    (globalChartRepresentative (deckRepresentation n) S k (doubleChartCutoff n k S χ η hχ hη hcη hsη w).val).val =
      fun x => η x • cutoffChartRaw n k S χ w x := by
  have h := globalChartRepresentative_chartCutoff n k S (η*χ) (hη.mul hχ) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη) w
  exact h.trans (funext (fun x => mul_smul (η x) (χ x)
    ((globalChartRepresentative (deckRepresentation n) S k w).val x)))

theorem quotientSupport_doubleChartCutoff (w : EquivariantForm (deckRepresentation n) univ k) :
    quotientSupport (doubleChartCutoff n k S χ η hχ hη hcη hsη w).val ⊆ (quotientChart S).symm '' tsupport η :=
  (quotientSupport_chartCutoff_image n k S (η*χ) (hη.mul hχ) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη) w).trans (image_mono tsupport_mul_subset_left)

def coreChartCodifferentialLimit (w : Core n (k+1)) : Core n k :=
  compactAdjoint n k (doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη w.val) -
    doubleChartCutoff n k S χ η hχ hη hcη hsη (compactAdjoint n k w).val

theorem quotientSupport_coreChartCodifferentialLimit (w : Core n (k+1)) :
    quotientSupport (coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w).val ⊆
      (quotientChart S).symm '' tsupport η :=
  (quotientSupport_sub _ _).trans (union_subset
    ((quotientSupport_equivariantAdjoint n k _).trans
      (quotientSupport_doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη w.val))
    (quotientSupport_doubleChartCutoff n k S χ η hχ hη hcη hsη (compactAdjoint n k w).val))

theorem globalChartRepresentative_coreChartCodifferentialLimit (w : Core n (k+1)) :
    (globalChartRepresentative (deckRepresentation n) S k
      (coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w).val).val =
      localAdjoint n k (fun x => η x • cutoffChartRaw n (k+1) S χ w.val x) -
        (fun x => η x • cutoffChartRaw n k S χ (compactAdjoint n k w).val x) := by
  let a := doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη w.val
  have hs := quotientSupport_chartCutoff n (k+1) S (η*χ) (hη.mul hχ) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη) w.val
  have hD := (globalChartRepresentative_compactAdjoint n k S a hs).trans
    (congrArg (localAdjoint n k) (globalChartRepresentative_doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη w.val))
  have hR := globalChartRepresentative_doubleChartCutoff n k S χ η hχ hη hcη hsη (compactAdjoint n k w).val
  exact (globalChartRepresentative_sub n k S _ _).trans
    (congrArg₂ (fun u v : Coordinates → FormValue n k => u-v) hD hR)

end TernaryPoly.PolynomialFormCoordinates
