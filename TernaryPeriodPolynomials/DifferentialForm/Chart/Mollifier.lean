module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Cutoff
public import TernaryPeriodPolynomials.Analysis.Compact.ChartExtension
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Mollifier
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity

@[expose] public section

/-! Genuine compact quotient chart smoothing from actual cutoffs and normalized convolution. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  CompactCoordinateIntegration
open scoped ContDiff

def convolvedChartRaw (n k : ℕ) (S : Space) (χ : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) : Coordinates → FormValue n k :=
  fun x => (coordinates n k).symm (fun i => scalarConvolution volume
    (CompactScalarMollifier.kernel Coordinates volume c)
    (components n k (cutoffChartRaw n k S χ w) i) x)

def mollifiedChartRaw (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) : Coordinates → FormValue n k :=
  fun x => η x • convolvedChartRaw n k S χ c w x

theorem contDiff_convolvedChartRaw (n k : ℕ) (S : Space) (χ : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    ContDiff ℝ ∞ (convolvedChartRaw n k S χ c w) := by
  change ContDiff ℝ ∞ ((coordinates n k).symm ∘ _)
  apply ContDiff.comp (𝕜 := ℝ) (E := Coordinates) (F := Index n k → ℝ) (G := FormValue n k)
    (ContinuousLinearEquiv.contDiff (𝕜 := ℝ) (E := Index n k → ℝ) (F := FormValue n k) (coordinates n k).symm)
  apply contDiff_pi.mpr
  intro i
  exact contDiff_scalarConvolution volume _ _
    (CompactScalarMollifier.kernel_contDiff Coordinates volume c)
    (CompactScalarMollifier.kernel_compact Coordinates volume c hc)
    (contDiff_cutoffChartComponents n k S χ hχ hsχ w i).continuous

theorem contDiff_mollifiedChartRaw (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (w : EquivariantForm (deckRepresentation n) univ k) :
    ContDiff ℝ ∞ (mollifiedChartRaw n k S χ η c w) := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  exact ContDiff.smul (𝕜 := ℝ) (𝕜' := ℝ) (E := Coordinates) (F := FormValue n k)
    hη (contDiff_convolvedChartRaw n k S χ c hc hχ hsχ w)

theorem tsupport_mollifiedChartRaw (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    tsupport (mollifiedChartRaw n k S χ η c w) ⊆ tsupport η :=
  tsupport_smul_subset_left η (convolvedChartRaw n k S χ c w)

/-- The actual smoothed chart form, zero off the outer cutoff support. -/
def mollifiedChartForm (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    Form (F := Coefficients n) (quotientChart S).target k :=
  ⟨mollifiedChartRaw n k S χ η c w,
    (contDiff_mollifiedChartRaw n k S χ η c hc hχ hsχ hη w).contDiffOn, by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsη (tsupport_mollifiedChartRaw n k S χ η c w h)))⟩

/-- This chart convolution is an actual global compact smooth local-coefficient form. -/
def chartMollifier (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    CompactSupportForm (deckRepresentation n) univ k :=
  compactChartExtend (deckRepresentation n) S (mollifiedChartForm n k S χ η c hc hχ hsχ hη hsη w)
    (hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_mollifiedChartRaw n k S χ η c w))
    ((tsupport_mollifiedChartRaw n k S χ η c w).trans hsη)

end TernaryPoly.PolynomialFormCoordinates
