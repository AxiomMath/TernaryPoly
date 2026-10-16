module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Regularizer
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Adjoint
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.SupportSub

@[expose] public section


/-! Literal compact differential and codifferential commutators with the actual chart regularizer. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c)

def coreChartDifferentialCommutator : Core n k →ₗ[ℝ] Core n (k+1) :=
  (compactDifferential (deckRepresentation n) isOpen_univ k).comp
    (coreChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc) -
  (coreChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc).comp
    (compactDifferential (deckRepresentation n) isOpen_univ k)

def coreChartCodifferentialCommutator : Core n (k+1) →ₗ[ℝ] Core n k :=
  (compactAdjoint n k).comp
    (coreChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc) -
  (coreChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc).comp (compactAdjoint n k)

theorem coreChartDifferentialCommutator_apply (w : Core n k) :
    coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w =
      compactDifferential (deckRepresentation n) isOpen_univ k
        (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val) -
      chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη
        (compactDifferential (deckRepresentation n) isOpen_univ k w).val := rfl

theorem coreChartCodifferentialCommutator_apply (w : Core n (k+1)) :
    coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w =
      compactAdjoint n k (chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val) -
      chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη (compactAdjoint n k w).val := rfl

theorem quotientSupport_coreChartDifferentialCommutator (w : Core n k) :
    quotientSupport (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val ⊆
      (quotientChart S).symm '' tsupport η :=
  (quotientSupport_sub _ _).trans (union_subset
    ((quotientSupport_differential isOpen_univ _).trans
      (quotientSupport_chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val))
    (quotientSupport_chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη
      (compactDifferential (deckRepresentation n) isOpen_univ k w).val))

theorem quotientSupport_coreChartCodifferentialCommutator (w : Core n (k+1)) :
    quotientSupport (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val ⊆
      (quotientChart S).symm '' tsupport η :=
  (quotientSupport_sub _ _).trans (union_subset
    ((quotientSupport_equivariantAdjoint n k _).trans
      (quotientSupport_chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val))
    (quotientSupport_chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη (compactAdjoint n k w).val))

end TernaryPoly.PolynomialFormCoordinates
