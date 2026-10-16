module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Commutators
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Adjoint

@[expose] public section


/-! Exact coordinate representatives of the true compact chart commutators. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

theorem globalChartRepresentative_sub (n k : ℕ) (S : Space)
    (a b : EquivariantForm (deckRepresentation n) univ k) :
    (globalChartRepresentative (deckRepresentation n) S k (a-b)).val =
      (globalChartRepresentative (deckRepresentation n) S k a).val -
        (globalChartRepresentative (deckRepresentation n) S k b).val :=
  congrArg (fun w : Form (F := Coefficients n) (quotientChart S).target k => w.val)
    ((globalChartRepresentative (deckRepresentation n) S k).map_sub a b)

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c)

theorem globalChartRepresentative_differentialCommutator (w : Core n k) :
    (globalChartRepresentative (deckRepresentation n) S (k+1)
      (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val).val =
      extDeriv (mollifiedChartRaw n k S χ η c w.val) -
        mollifiedChartRaw n (k+1) S χ η c (compactDifferential (deckRepresentation n) isOpen_univ k w).val := by
  let a := chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val
  have hs := quotientSupport_chartMollifier_source n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val
  have hD := (globalChartRepresentative_compactDifferential n k S a hs).trans
    (congrArg extDeriv (globalChartRepresentative_chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val))
  have hR := globalChartRepresentative_chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη
    (compactDifferential (deckRepresentation n) isOpen_univ k w).val
  exact (globalChartRepresentative_sub n (k+1) S _ _).trans
    (congrArg₂ (fun u v : Coordinates → FormValue n (k+1) => u-v) hD hR)

theorem globalChartRepresentative_codifferentialCommutator (w : Core n (k+1)) :
    (globalChartRepresentative (deckRepresentation n) S k
      (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w).val).val =
      localAdjoint n k (mollifiedChartRaw n (k+1) S χ η c w.val) -
        mollifiedChartRaw n k S χ η c (compactAdjoint n k w).val := by
  let a := chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val
  have hs := quotientSupport_chartMollifier_source n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val
  have hD := (globalChartRepresentative_compactAdjoint n k S a hs).trans
    (congrArg (localAdjoint n k) (globalChartRepresentative_chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val))
  have hR := globalChartRepresentative_chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη (compactAdjoint n k w).val
  exact (globalChartRepresentative_sub n k S _ _).trans
    (congrArg₂ (fun u v : Coordinates → FormValue n k => u-v) hD hR)

end TernaryPoly.PolynomialFormCoordinates
