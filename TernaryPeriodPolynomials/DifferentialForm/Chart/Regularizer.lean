module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Linear

@[expose] public section

/-! The actual compact chart mollifier as a linear map on genuine quotient forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target)

include hcχ in
theorem chartMollifier_add (w z : EquivariantForm (deckRepresentation n) univ k) :
    chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη (w+z) =
      chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w +
      chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη z := by
  let R := chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη
  let G := globalChartRepresentative (deckRepresentation n) S k
  have hS (a) := quotientSupport_chartMollifier_source n k S χ η c hc hχ hsχ hη hcη hsη a
  apply Subtype.ext
  apply eq_of_globalChartRepresentative_eq (deckRepresentation n) S _ _ (hS (w+z))
    ((quotientSupport_add (R w).val (R z).val).trans (union_subset (hS w) (hS z)))
  apply Subtype.ext
  calc
    (G (R (w+z)).val).val = mollifiedChartRaw n k S χ η c (w+z) :=
      globalChartRepresentative_chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη _
    _ = mollifiedChartRaw n k S χ η c w + mollifiedChartRaw n k S χ η c z :=
      mollifiedChartRaw_add n k S χ η c hχ hcχ hsχ w z
    _ = (G (R w).val).val + (G (R z).val).val := by
      rw [globalChartRepresentative_chartMollifier, globalChartRepresentative_chartMollifier]
    _ = (G ((R w).val + (R z).val)).val :=
      (congrArg (fun a : Form (F := Coefficients n) (quotientChart S).target k => a.val)
        (G.map_add (R w).val (R z).val)).symm

omit hcχ in
theorem chartMollifier_smul (a : ℝ) (w : EquivariantForm (deckRepresentation n) univ k) :
    chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη (a • w) =
      a • chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w := by
  let R := chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη
  let G := globalChartRepresentative (deckRepresentation n) S k
  have hS (z) := quotientSupport_chartMollifier_source n k S χ η c hc hχ hsχ hη hcη hsη z
  apply Subtype.ext
  apply eq_of_globalChartRepresentative_eq (deckRepresentation n) S _ _ (hS (a • w))
    ((quotientSupport_smul a (R w).val).trans (hS w))
  apply Subtype.ext
  calc
    (G (R (a • w)).val).val = mollifiedChartRaw n k S χ η c (a • w) :=
      globalChartRepresentative_chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη _
    _ = a • mollifiedChartRaw n k S χ η c w := mollifiedChartRaw_smul n k S χ η c a w
    _ = a • (G (R w).val).val := by rw [globalChartRepresentative_chartMollifier]
    _ = (G (a • (R w).val)).val :=
      (congrArg (fun z : Form (F := Coefficients n) (quotientChart S).target k => z.val)
        (G.map_smul a (R w).val)).symm

/-- No boundedness hypothesis is used to construct this literal compact smoothing map. -/
def chartRegularizer : EquivariantForm (deckRepresentation n) univ k →ₗ[ℝ]
    CompactSupportForm (deckRepresentation n) univ k where
  toFun := chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη
  map_add' := chartMollifier_add n k S χ η c hc hχ hcχ hsχ hη hcη hsη
  map_smul' := chartMollifier_smul n k S χ η c hc hχ hsχ hη hcη hsη

end TernaryPoly.PolynomialFormCoordinates
