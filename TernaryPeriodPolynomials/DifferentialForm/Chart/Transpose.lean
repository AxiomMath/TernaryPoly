module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.DualInput
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Mollifier
public import TernaryPeriodPolynomials.Analysis.Compact.ChartExtension

@[expose] public section


/-! Actual compact smooth transpose of the quotient chart regularizer. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff

def chartTransposeComponents (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) : Index n k → Coordinates → ℝ :=
  weightedCutoffTranspose volume (weightedGram n k) (CompactScalarMollifier.kernel Coordinates volume c)
    χ η (components n k (globalChartRepresentative (deckRepresentation n) S k w).val)

theorem tsupport_chartTransposeComponents (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    tsupport (chartTransposeComponents n k S χ η c w i) ⊆ tsupport χ :=
  tsupport_mul_subset_left

theorem contDiff_chartTransposeComponents (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    ContDiff ℝ ∞ (chartTransposeComponents n k S χ η c w i) := by
  apply contDiff_of_tsupport_subset isOpen_positiveCoordinates _
    ((tsupport_chartTransposeComponents n k S χ η c w i).trans (hsχ.trans (quotientChart_target_subset S)))
  apply hχ.contDiffOn.mul
  apply contDiffOn_metricDual
  · intro j l
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram_inverse n k) j) l
  · intro j
    exact (contDiff_scalarConvolution volume _ (chartDualInput n k S η w j)
      ((CompactScalarMollifier.kernel_contDiff Coordinates volume c).comp contDiff_neg)
      ((CompactScalarMollifier.kernel_compact Coordinates volume c hc).comp_homeomorph (Homeomorph.neg Coordinates))
      (contDiff_chartDualInput n k S η hη hsη w j).continuous).contDiffOn

def chartTransposeRaw (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) (x : Coordinates) : FormValue n k :=
  (coordinates n k).symm (fun i => chartTransposeComponents n k S χ η c w i x)

theorem components_chartTransposeRaw (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    components n k (chartTransposeRaw n k S χ η c w) = chartTransposeComponents n k S χ η c w := by
  funext i x
  exact congrFun ((coordinates n k).apply_symm_apply (fun j => chartTransposeComponents n k S χ η c w j x)) i

theorem tsupport_chartTransposeRaw (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    tsupport (chartTransposeRaw n k S χ η c w) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  apply hx
  have hv : (fun i => chartTransposeComponents n k S χ η c w i x) = 0 := by
    funext i
    exact image_eq_zero_of_notMem_tsupport
      (fun hi => hn (tsupport_chartTransposeComponents n k S χ η c w i hi))
  change (coordinates n k).symm _ = 0
  rw [hv, map_zero]

theorem contDiff_chartTransposeRaw (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    ContDiff ℝ ∞ (chartTransposeRaw n k S χ η c w) := by
  change ContDiff ℝ ∞ ((coordinates n k).symm ∘ _)
  apply ContDiff.comp (𝕜 := ℝ) (E := Coordinates) (F := Index n k → ℝ) (G := FormValue n k)
    (ContinuousLinearEquiv.contDiff (𝕜 := ℝ) (E := Index n k → ℝ) (F := FormValue n k) (coordinates n k).symm)
  exact contDiff_pi.mpr (fun i => contDiff_chartTransposeComponents n k S χ η c hc hχ hsχ hη hsη w i)

def chartTransposeForm (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    Form (F := Coefficients n) (quotientChart S).target k :=
  ⟨chartTransposeRaw n k S χ η c w,
    (contDiff_chartTransposeRaw n k S χ η c hc hχ hsχ hη hsη w).contDiffOn, by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsχ (tsupport_chartTransposeRaw n k S χ η c w h)))⟩

def chartTranspose (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    CompactSupportForm (deckRepresentation n) univ k :=
  compactChartExtend (deckRepresentation n) S (chartTransposeForm n k S χ η c hc hχ hsχ hη hsη w)
    (hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartTransposeRaw n k S χ η c w))
    ((tsupport_chartTransposeRaw n k S χ η c w).trans hsχ)

end TernaryPoly.PolynomialFormCoordinates
