module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.FormalAdjoint

@[expose] public section


/-! Genuine finite matrix differential expressions and their transpose divergence identity. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- Coefficient arrays allow every finite first-order matrix differential operator. -/
def matrixFirstOrder (v : K → E) (a b : J → I → K → E → ℝ)
    (f : I → E → ℝ) (j : J) (x : E) : ℝ :=
  ∑ i, ∑ k, firstOrder (v k) (a j i k) (b j i k) (f i) x

/-- The explicit transposed matrix divergence, before multiplication by the inverse metric. -/
def matrixTranspose (v : K → E) (a b : J → I → K → E → ℝ)
    (g : J → E → ℝ) (i : I) (x : E) : ℝ :=
  ∑ j, ∑ k, transposeOrder (v k) (a j i k) (b j i k) (g j) x

/-- Genuine integration by parts for every finite first-order matrix expression. -/
theorem integral_matrixFirstOrder (v : K → E) (a b : J → I → K → E → ℝ)
    (f : I → E → ℝ) (g : J → E → ℝ)
    (ha : ∀ j i k, ContDiff ℝ 1 (a j i k)) (hb : ∀ j i k, Continuous (b j i k))
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hg : ∀ j, ContDiff ℝ 1 (g j))
    (hc : ∀ i, HasCompactSupport (f i)) :
    ∫ x, ∑ j, matrixFirstOrder v a b f j x * g j x ∂μ =
      ∫ x, ∑ i, f i x * matrixTranspose v a b g i x ∂μ := by
  have hL j i k : Integrable (fun x => firstOrder (v k) (a j i k) (b j i k) (f i) x * g j x) μ :=
    ((continuous_firstOrder (v k) (ha j i k).continuous (hb j i k) (hf i)).mul
      (hg j).continuous).integrable_of_hasCompactSupport
        (compact_firstOrder (v k) (a j i k) (b j i k) (hc i)).mul_right
  have hR i j k : Integrable (fun x => f i x * transposeOrder (v k) (a j i k) (b j i k) (g j) x) μ :=
    ((hf i).continuous.mul (continuous_transposeOrder (v k) (ha j i k) (hb j i k) (hg j))).integrable_of_hasCompactSupport (hc i).mul_right
  simp only [matrixFirstOrder, matrixTranspose, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ j, ∑ i, ∑ k, ∫ x, firstOrder (v k) (a j i k) (b j i k) (f i) x * g j x ∂μ := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hL j i k)))]
      apply Finset.sum_congr rfl; intro j _
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hL j i k))]
      apply Finset.sum_congr rfl; intro i _
      exact integral_finsetSum _ (fun k _ => hL j i k)
    _ = ∑ i, ∑ j, ∑ k, ∫ x, f i x * transposeOrder (v k) (a j i k) (b j i k) (g j) x ∂μ := by
      simp_rw [integral_firstOrder_mul _ (ha _ _ _) (hb _ _ _) (hf _) (hg _) (hc _)]
      exact Finset.sum_comm
    _ = _ := by
      symm
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hR i j k)))]
      apply Finset.sum_congr rfl; intro i _
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hR i j k))]
      apply Finset.sum_congr rfl; intro j _
      exact integral_finsetSum _ (fun k _ => hR i j k)

end TernaryPoly.CompactCoordinateIntegration
