module

public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FriedrichsIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.DoubleCutoffCommutatorRegularity

@[expose] public section

/-! The actual localized finite matrix commutator is a finite sum of scalar ones. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype I] [Fintype K]

omit [FiniteDimensional ℝ E] in
theorem matrix_double_cutoff_commutator (κ χ η : E → ℝ) (v : K → E)
    (a b : J → I → K → E → ℝ) (f : I → E → ℝ)
    (hκ : Continuous κ) (ha : ∀ j i k, Continuous (a j i k)) (hb : ∀ j i k, Continuous (b j i k))
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (j : J) (x : E) :
    matrixFirstOrder v a b (fun i y => η y * scalarConvolution μ κ (fun z => χ z * f i z) y) j x -
      η x * scalarConvolution μ κ (fun z => χ z * matrixFirstOrder v a b f j z) x =
      ∑ i, ∑ k, doubleCutoffCommutator μ κ (v k) (a j i k) (b j i k) χ η (f i) x := by
  have hD (i : I) (k : K) : Continuous (fun z => χ z * firstOrder (v k) (a j i k) (b j i k) (f i) z) :=
    hχ.mul (continuous_firstOrder (v k) (ha j i k) (hb j i k) (hf i))
  have hcD (i : I) (k : K) : HasCompactSupport (fun z => χ z * firstOrder (v k) (a j i k) (b j i k) (f i) z) :=
    hcχ.mul_right
  have hcDs (i : I) : HasCompactSupport (fun y => ∑ k, χ y * firstOrder (v k) (a j i k) (b j i k) (f i) y) := by
    have he : (fun y => ∑ k, χ y * firstOrder (v k) (a j i k) (b j i k) (f i) y) =
        ∑ k, (fun y => χ y * firstOrder (v k) (a j i k) (b j i k) (f i) y) := by
      funext y; simp only [Finset.sum_apply]
    rw [he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (fun (k : K) _ => hcD i k)
  have hDs (i : I) : Continuous (fun y => ∑ k, χ y * firstOrder (v k) (a j i k) (b j i k) (f i) y) :=
    continuous_finsetSum Finset.univ (fun k _ => hD i k)
  have hsum : scalarConvolution μ κ (fun z => χ z * matrixFirstOrder v a b f j z) x =
      ∑ i, ∑ k, scalarConvolution μ κ (fun z => χ z * firstOrder (v k) (a j i k) (b j i k) (f i) z) x := by
    unfold matrixFirstOrder
    simp_rw [Finset.mul_sum]
    rw [scalarConvolution_finsetSum μ Finset.univ κ _ hκ (fun i _ => hDs i) (fun i _ => hcDs i)]
    apply Finset.sum_congr rfl
    intro i _
    exact scalarConvolution_finsetSum μ Finset.univ κ _ hκ (fun k _ => hD i k) (fun k _ => hcD i k) x
  rw [hsum]
  simp only [matrixFirstOrder, doubleCutoffCommutator, Finset.sum_sub_distrib, Finset.mul_sum]

end TernaryPoly.CompactCoordinateIntegration
