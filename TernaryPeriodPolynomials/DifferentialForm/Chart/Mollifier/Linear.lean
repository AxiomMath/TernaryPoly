module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionLinear
public import TernaryPeriodPolynomials.Analysis.Compact.ChartDetermination

@[expose] public section


/-! Actual linearity of the quotient chart convolution construction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  CompactCoordinateIntegration
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)

theorem cutoffChartComponents_add (w z : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    components n k (cutoffChartRaw n k S χ (w+z)) i =
      components n k (cutoffChartRaw n k S χ w) i + components n k (cutoffChartRaw n k S χ z) i := by
  funext x
  simp only [components, cutoffChartRaw, map_add, AddMemClass.coe_add, Pi.add_apply, smul_add]

theorem cutoffChartComponents_smul (a : ℝ) (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    components n k (cutoffChartRaw n k S χ (a • w)) i =
      a • components n k (cutoffChartRaw n k S χ w) i := by
  funext x
  simp only [components, cutoffChartRaw, map_smul, SetLike.val_smul, Pi.smul_apply,
    smul_comm (χ x) a]

theorem mollifiedChartRaw_add (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (w z : EquivariantForm (deckRepresentation n) univ k) :
    mollifiedChartRaw n k S χ η c (w+z) =
      mollifiedChartRaw n k S χ η c w + mollifiedChartRaw n k S χ η c z := by
  have hh (i : Index n k) := scalarConvolution_add volume
    (CompactScalarMollifier.kernel Coordinates volume c)
    (components n k (cutoffChartRaw n k S χ w) i)
    (components n k (cutoffChartRaw n k S χ z) i)
    (CompactScalarMollifier.kernel_contDiff Coordinates volume c).continuous
    (contDiff_cutoffChartComponents n k S χ hχ hsχ w i).continuous
    (contDiff_cutoffChartComponents n k S χ hχ hsχ z i).continuous
    (compact_cutoffChartComponents n k S χ hcχ w i)
    (compact_cutoffChartComponents n k S χ hcχ z i)
  funext x
  let v (a : EquivariantForm (deckRepresentation n) univ k) : Index n k → ℝ := fun i =>
    scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
      (components n k (cutoffChartRaw n k S χ a) i) x
  let L : (Index n k → ℝ) →ₗ[ℝ] FormValue n k := η x • (coordinates n k).symm.toLinearMap
  have hv : v (w+z) = v w + v z := by
    funext i
    exact (congrArg (fun f => scalarConvolution volume
      (CompactScalarMollifier.kernel Coordinates volume c) f x)
      (cutoffChartComponents_add n k S χ w z i)).trans (congrFun (hh i) x)
  change L (v (w+z)) = L (v w) + L (v z)
  exact (congrArg L hv).trans (L.map_add (v w) (v z))

theorem mollifiedChartRaw_smul (a : ℝ) (w : EquivariantForm (deckRepresentation n) univ k) :
    mollifiedChartRaw n k S χ η c (a • w) = a • mollifiedChartRaw n k S χ η c w := by
  funext x
  let v (z : EquivariantForm (deckRepresentation n) univ k) : Index n k → ℝ := fun i =>
    scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
      (components n k (cutoffChartRaw n k S χ z) i) x
  let L : (Index n k → ℝ) →ₗ[ℝ] FormValue n k := η x • (coordinates n k).symm.toLinearMap
  have hv : v (a • w) = a • v w := by
    funext i
    exact (congrArg (fun f => scalarConvolution volume
      (CompactScalarMollifier.kernel Coordinates volume c) f x)
      (cutoffChartComponents_smul n k S χ a w i)).trans
      (congrFun (scalarConvolution_smul volume _ _ a) x)
  change L (v (a • w)) = a • L (v w)
  exact (congrArg L hv).trans (L.map_smul a (v w))

end TernaryPoly.PolynomialFormCoordinates
