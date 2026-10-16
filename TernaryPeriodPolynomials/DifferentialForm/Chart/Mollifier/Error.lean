module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier

@[expose] public section


/-! Support and smoothness of the actual localized chart mollification error. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff

def mollifiedChartError (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) : Coordinates → FormValue n k :=
  fun x => η x • (convolvedChartRaw n k S χ c w x - cutoffChartRaw n k S χ w x)

theorem mollifiedChartError_apply (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) (x : Coordinates) :
    mollifiedChartError n k S χ η c w x =
      mollifiedChartRaw n k S χ η c w x - η x • cutoffChartRaw n k S χ w x :=
  smul_sub (η x) (convolvedChartRaw n k S χ c w x) (cutoffChartRaw n k S χ w x)

theorem tsupport_mollifiedChartError (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    tsupport (mollifiedChartError n k S χ η c w) ⊆ tsupport η := by
  have h := tsupport_smul_subset_left η
    (fun x : Coordinates => convolvedChartRaw n k S χ c w x - cutoffChartRaw n k S χ w x)
  exact h

theorem contDiff_mollifiedChartError (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (w : EquivariantForm (deckRepresentation n) univ k) :
    ContDiff ℝ ∞ (mollifiedChartError n k S χ η c w) := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  exact ContDiff.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates) (F := FormValue n k) hη
    ((contDiff_convolvedChartRaw n k S χ c hc hχ hsχ w).sub
      (contDiff_cutoffChartRaw n k S χ hχ hsχ w))

end TernaryPoly.PolynomialFormCoordinates
