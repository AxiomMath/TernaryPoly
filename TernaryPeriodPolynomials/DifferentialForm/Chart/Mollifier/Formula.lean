module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier

@[expose] public section


/-! Literal coordinate and support formulas for the actual quotient chart regularizer. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  CompactCoordinateIntegration
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k)

theorem globalChartRepresentative_chartMollifier :
    (globalChartRepresentative (deckRepresentation n) S k
      (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w).val).val =
        mollifiedChartRaw n k S χ η c w := by
  exact congrArg (fun z : Form (F := Coefficients n) (quotientChart S).target k => z.val)
    (globalChartRepresentative_compactChartExtend (deckRepresentation n) S
      (mollifiedChartForm n k S χ η c hc hχ hsχ hη hsη w)
      (hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_mollifiedChartRaw n k S χ η c w))
      ((tsupport_mollifiedChartRaw n k S χ η c w).trans hsη))

theorem quotientSupport_chartMollifier :
    quotientSupport (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w).val ⊆
      (quotientChart S).symm '' tsupport η :=
  (quotientSupport_compactChartExtend (deckRepresentation n) S
    (mollifiedChartForm n k S χ η c hc hχ hsχ hη hsη w)
    (hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_mollifiedChartRaw n k S χ η c w))
    ((tsupport_mollifiedChartRaw n k S χ η c w).trans hsη)).trans
    (image_mono (tsupport_mollifiedChartRaw n k S χ η c w))

theorem quotientSupport_chartMollifier_source :
    quotientSupport (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w).val ⊆
      (quotientChart S).source := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := quotientSupport_chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w hq
  exact (quotientChart S).map_target (hsη hx)

omit hc hχ hsχ hη hcη hsη in
theorem components_mollifiedChartRaw (i : Index n k) (x : Coordinates) :
    components n k (mollifiedChartRaw n k S χ η c w) i x =
      η x * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (components n k (cutoffChartRaw n k S χ w) i) x := by
  change (coordinates n k (η x • (coordinates n k).symm _)) i = _
  rw [map_smul, (coordinates n k).apply_symm_apply]
  rfl

end TernaryPoly.PolynomialFormCoordinates
