module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionTranspose
public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.MatrixAdjoint

@[expose] public section

/-! Actual weighted transposition of cutoff convolution, retaining the inverse metric. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Set MeasureTheory
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype I] [DecidableEq I]

def cutoffConvolution (κ χ η : E → ℝ) (f : I → E → ℝ) (i : I) (x : E) : ℝ :=
  η x * scalarConvolution μ κ (fun y => χ y * f i y) x

def weightedCutoffTranspose (M : E → Matrix I I ℝ) (κ χ η : E → ℝ)
    (g : I → E → ℝ) (i : I) (x : E) : ℝ :=
  χ x * metricDual (fun y => (M y)⁻¹)
    (fun j => scalarConvolution μ (fun z => κ (-z)) (fun y => η y * metricDual M g j y)) i x

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem metricDual_weightedCutoffTranspose (M : E → Matrix I I ℝ) (κ χ η : E → ℝ)
    (hM : ∀ x ∈ tsupport χ, IsUnit (M x).det) (g : I → E → ℝ) (i : I) (x : E) :
    metricDual M (weightedCutoffTranspose μ M κ χ η g) i x =
      χ x * scalarConvolution μ (fun z => κ (-z)) (fun y => η y * metricDual M g i y) x := by
  by_cases hx : χ x = 0
  · simp [metricDual, weightedCutoffTranspose, hx, Matrix.mulVec, dotProduct]
  · let v : I → ℝ := fun j => scalarConvolution μ (fun z => κ (-z))
      (fun y => η y * metricDual M g j y) x
    change ((M x).mulVec (χ x • ((M x)⁻¹.mulVec v))) i = χ x * v i
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (hM x (subset_tsupport χ hx)), Matrix.one_mulVec]
    rfl

theorem integral_weightedCutoffTranspose (M : E → Matrix I I ℝ) (κ χ η : E → ℝ)
    (hM : ∀ x ∈ tsupport χ, IsUnit (M x).det) (hκ : ContDiff ℝ 0 κ)
    (hcκ : HasCompactSupport κ) (f g : I → E → ℝ)
    (hf : ∀ i, Continuous (fun x => χ x * f i x))
    (hcf : ∀ i, HasCompactSupport (fun x => χ x * f i x))
    (hg : ∀ i, Continuous (fun x => η x * metricDual M g i x))
    (hcg : ∀ i, HasCompactSupport (fun x => η x * metricDual M g i x)) :
    ∫ x, weightedPairing M (cutoffConvolution μ κ χ η f) g x ∂μ =
      ∫ x, weightedPairing M f (weightedCutoffTranspose μ M κ χ η g) x ∂μ := by
  let F (i : I) (x : E) := χ x * f i x
  let G (i : I) (x : E) := η x * metricDual M g i x
  have hκr : ContDiff ℝ 0 (fun z => κ (-z)) := hκ.comp contDiff_neg
  have hcκr : HasCompactSupport (fun z => κ (-z)) := hcκ.comp_homeomorph (Homeomorph.neg E)
  have hL i : Integrable (fun x => scalarConvolution μ κ (F i) x * G i x) μ :=
    ((contDiff_scalarConvolution μ κ (F i) hκ hcκ (hf i)).continuous.mul (hg i)).integrable_of_hasCompactSupport
      (hcg i).mul_left
  have hR i : Integrable (fun x => F i x * scalarConvolution μ (fun z => κ (-z)) (G i) x) μ :=
    ((hf i).mul (contDiff_scalarConvolution μ _ (G i) hκr hcκr (hg i)).continuous).integrable_of_hasCompactSupport
      (hcf i).mul_right
  have hleft (x : E) : weightedPairing M (cutoffConvolution μ κ χ η f) g x =
      ∑ i, scalarConvolution μ κ (F i) x * G i x := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [cutoffConvolution, F, G]
    ring
  have hright (x : E) : weightedPairing M f (weightedCutoffTranspose μ M κ χ η g) x =
      ∑ i, F i x * scalarConvolution μ (fun z => κ (-z)) (G i) x := by
    unfold weightedPairing
    apply Finset.sum_congr rfl
    intro i _
    rw [metricDual_weightedCutoffTranspose μ M κ χ η hM g i x]
    dsimp [F, G]
    ring
  simp_rw [hleft, hright]
  rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hR i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_scalarConvolution_mul μ κ (F i) (G i) hκ.continuous (hf i) (hg i) (hcf i) (hcg i)

end TernaryPoly.CompactCoordinateIntegration
