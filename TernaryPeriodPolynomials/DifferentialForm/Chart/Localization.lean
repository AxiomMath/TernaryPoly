module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Cutoff
public import TernaryPeriodPolynomials.Analysis.Compact.ChartExtension

@[expose] public section

/-! Genuine compact localization of a quotient form by a coordinate cutoff. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)

def cutoffChartForm (w : EquivariantForm (deckRepresentation n) univ k) :
    Form (F := Coefficients n) (quotientChart S).target k :=
  ⟨cutoffChartRaw n k S χ w, (contDiff_cutoffChartRaw n k S χ hχ hsχ w).contDiffOn, by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsχ (tsupport_cutoffChartRaw n k S χ w h)))⟩

def chartCutoff (w : EquivariantForm (deckRepresentation n) univ k) :
    CompactSupportForm (deckRepresentation n) univ k :=
  compactChartExtend (deckRepresentation n) S (cutoffChartForm n k S χ hχ hsχ w)
    (compact_cutoffChartRaw n k S χ hcχ w) ((tsupport_cutoffChartRaw n k S χ w).trans hsχ)

theorem globalChartRepresentative_chartCutoff (w : EquivariantForm (deckRepresentation n) univ k) :
    (globalChartRepresentative (deckRepresentation n) S k (chartCutoff n k S χ hχ hcχ hsχ w).val).val =
      cutoffChartRaw n k S χ w :=
  congrArg (fun a : Form (F := Coefficients n) (quotientChart S).target k => a.val)
    (globalChartRepresentative_compactChartExtend (deckRepresentation n) S
      (cutoffChartForm n k S χ hχ hsχ w)
      (compact_cutoffChartRaw n k S χ hcχ w) ((tsupport_cutoffChartRaw n k S χ w).trans hsχ))

theorem quotientSupport_chartCutoff (w : EquivariantForm (deckRepresentation n) univ k) :
    quotientSupport (chartCutoff n k S χ hχ hcχ hsχ w).val ⊆ (quotientChart S).source := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := quotientSupport_compactChartExtend (deckRepresentation n) S
    (cutoffChartForm n k S χ hχ hsχ w)
    (compact_cutoffChartRaw n k S χ hcχ w) ((tsupport_cutoffChartRaw n k S χ w).trans hsχ) hq
  exact (quotientChart S).map_target (hsχ (tsupport_cutoffChartRaw n k S χ w hx))

theorem chartCutoff_apply (w : EquivariantForm (deckRepresentation n) univ k)
    {x : Coordinates} (hx : x ∈ (quotientChart S).target) :
    (chartCutoff n k S χ hχ hcχ hsχ w).val.val.val x = χ x • w.val.val x := by
  have h := congrFun (globalChartRepresentative_chartCutoff n k S χ hχ hcχ hsχ w) x
  have he := globalChartRepresentative_apply (deckRepresentation n) S
    (chartCutoff n k S χ hχ hcχ hsχ w).val hx
  have hw := globalChartRepresentative_apply (deckRepresentation n) S w hx
  exact he.symm.trans (h.trans (congrArg (χ x • ·) hw))

end TernaryPoly.PolynomialFormCoordinates
