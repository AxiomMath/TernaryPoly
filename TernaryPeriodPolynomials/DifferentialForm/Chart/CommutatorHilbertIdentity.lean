module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartDerivative
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartCodifferential
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartDifferentialCommutator
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartCodifferentialCommutator

@[expose] public section


/-! Literal bounded Hilbert commutator identities on genuine compact inclusions. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c)

theorem hilbertChartDifferential_sub_commutator (w : Core n k) :
    hilbertChartDifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n k w) -
      hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n k w) =
    hilbertChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc
      (inclusion n (k+1) (compactDifferential (deckRepresentation n) isOpen_univ k w)) := by
  let d := compactDifferential (deckRepresentation n) isOpen_univ k
  let a := chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val
  let b := chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη (d w).val
  have hC := (hilbertChartDifferentialCommutator_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).trans
    ((congrArg (inclusion n (k+1))
      (coreChartDifferentialCommutator_apply n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)).trans
      ((inclusion n (k+1)).map_sub (d a) b))
  have hV := hilbertChartDifferential_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη c hc w
  have hR := hilbertChartRegularizer_inclusion n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc (d w)
  exact (congrArg₂ (fun u v : Hilbert n (k+1) => u-v) hV hC).trans
    ((sub_sub_cancel (inclusion n (k+1) (d a)) (inclusion n (k+1) b)).trans hR.symm)

theorem hilbertChartCodifferential_sub_commutator (w : Core n (k+1)) :
    hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n (k+1) w) -
      hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n (k+1) w) =
    hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc
      (inclusion n k (compactAdjoint n k w)) := by
  let d := compactAdjoint n k
  let a := chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val
  let b := chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη (d w).val
  have hC := (hilbertChartCodifferentialCommutator_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).trans
    ((congrArg (inclusion n k)
      (coreChartCodifferentialCommutator_apply n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)).trans
      ((inclusion n k).map_sub (d a) b))
  have hV := hilbertChartCodifferential_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη c hc w
  have hR := hilbertChartRegularizer_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη c hc (d w)
  exact (congrArg₂ (fun u v : Hilbert n k => u-v) hV hC).trans
    ((sub_sub_cancel (inclusion n k (d a)) (inclusion n k b)).trans hR.symm)

end TernaryPoly.PolynomialFormCoordinates
