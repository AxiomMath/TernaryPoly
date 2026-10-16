module

public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FormalAdjoint
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionSum

@[expose] public section


/-! The actual matrix smoothing commutator is exactly a finite sum of the scalar commutators. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype I] [Fintype K]

omit [FiniteDimensional ℝ E] in
theorem matrixFirstOrder_convolution_commutator (κ : E → ℝ) (v : K → E)
    (a b : J → I → K → E → ℝ) (f : I → E → ℝ)
    (hκ : Continuous κ) (ha : ∀ j i k, Continuous (a j i k)) (hb : ∀ j i k, Continuous (b j i k))
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hcf : ∀ i, HasCompactSupport (f i)) (j : J) (x : E) :
    matrixFirstOrder v a b (fun i => scalarConvolution μ κ (f i)) j x -
      scalarConvolution μ κ (matrixFirstOrder v a b f j) x =
      ∑ i, ∑ k, (firstOrder (v k) (a j i k) (b j i k) (scalarConvolution μ κ (f i)) x -
        scalarConvolution μ κ (firstOrder (v k) (a j i k) (b j i k) (f i)) x) := by
  have hD (i : I) (k : K) : Continuous (firstOrder (v k) (a j i k) (b j i k) (f i)) :=
    continuous_firstOrder (v k) (ha j i k) (hb j i k) (hf i)
  have hcD (i : I) (k : K) : HasCompactSupport (firstOrder (v k) (a j i k) (b j i k) (f i)) :=
    compact_firstOrder (v k) (a j i k) (b j i k) (hcf i)
  have hcDs (i : I) : HasCompactSupport (fun y => ∑ k, firstOrder (v k) (a j i k) (b j i k) (f i) y) := by
    have he : (fun y => ∑ k, firstOrder (v k) (a j i k) (b j i k) (f i) y) =
        ∑ k, firstOrder (v k) (a j i k) (b j i k) (f i) := by
      funext y
      simp only [Finset.sum_apply]
    rw [he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (fun (k : K) _ => hcD i k)
  have hDs (i : I) : Continuous (fun y => ∑ k, firstOrder (v k) (a j i k) (b j i k) (f i) y) :=
    continuous_finsetSum Finset.univ (fun k _ => hD i k)
  have hsum : scalarConvolution μ κ (matrixFirstOrder v a b f j) x =
      ∑ i, ∑ k, scalarConvolution μ κ (firstOrder (v k) (a j i k) (b j i k) (f i)) x := by
    unfold matrixFirstOrder
    rw [scalarConvolution_finsetSum μ Finset.univ κ _ hκ
      (fun i _ => hDs i) (fun i _ => hcDs i)]
    apply Finset.sum_congr rfl
    intro i _
    exact scalarConvolution_finsetSum μ Finset.univ κ _ hκ (fun k _ => hD i k) (fun k _ => hcD i k) x
  rw [hsum]
  simp only [matrixFirstOrder, Finset.sum_sub_distrib]

end TernaryPoly.CompactCoordinateIntegration
