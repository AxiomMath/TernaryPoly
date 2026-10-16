module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Transpose

@[expose] public section


/-! Exact coordinate and support laws for the actual compact chart transpose. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k)

theorem globalChartRepresentative_chartTranspose :
    (globalChartRepresentative (deckRepresentation n) S k
      (chartTranspose n k S χ η c hc hχ hcχ hsχ hη hsη w).val).val =
        chartTransposeRaw n k S χ η c w :=
  congrArg (fun z : Form (F := Coefficients n) (quotientChart S).target k => z.val)
    (globalChartRepresentative_compactChartExtend (deckRepresentation n) S
      (chartTransposeForm n k S χ η c hc hχ hsχ hη hsη w)
      (hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartTransposeRaw n k S χ η c w))
      ((tsupport_chartTransposeRaw n k S χ η c w).trans hsχ))

theorem quotientSupport_chartTranspose_source :
    quotientSupport (chartTranspose n k S χ η c hc hχ hcχ hsχ hη hsη w).val ⊆
      (quotientChart S).source := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := quotientSupport_compactChartExtend (deckRepresentation n) S
    (chartTransposeForm n k S χ η c hc hχ hsχ hη hsη w)
    (hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartTransposeRaw n k S χ η c w))
    ((tsupport_chartTransposeRaw n k S χ η c w).trans hsχ) hq
  exact (quotientChart S).map_target (hsχ (tsupport_chartTransposeRaw n k S χ η c w hx))

end TernaryPoly.PolynomialFormCoordinates
