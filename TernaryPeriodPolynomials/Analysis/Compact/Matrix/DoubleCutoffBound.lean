module

public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.DoubleCutoffCommutatorBound
public import TernaryPeriodPolynomials.Analysis.Finite.IntegralSquare
public import Mathlib.Tactic.Choose

@[expose] public section

/-! One scale- and input-independent L2 bound for each actual matrix-output component. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory CompactCoordinateIntegration
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype I] [Fintype K]

/-- Actual matrix regularizers satisfy a single L2 bound independent of scale and input. -/
theorem matrix_double_cutoff_uniform (χ η : E → ℝ) (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (v : K → E) (a b : J → I → K → E → ℝ)
    (ha : ∀ j i k, ContDiff ℝ 1 (a j i k)) (hb : ∀ j i k, Continuous (b j i k))
    (hca : ∀ j i k, HasCompactSupport (a j i k)) (hcb : ∀ j i k, HasCompactSupport (b j i k)) (j : J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : I → E → ℝ), (∀ i, ContDiff ℝ 1 (f i)) →
      (∀ i, HasCompactSupport (f i)) → ∀ (c : ℝ), 0 < c →
        ∫ x, ‖matrixFirstOrder v a b (fun i y => η y * scalarConvolution μ (kernel E μ c) (fun z => χ z * f i z) y) j x -
          η x * scalarConvolution μ (kernel E μ c) (fun z => χ z * matrixFirstOrder v a b f j z) x‖ ^ 2 ∂μ ≤
          C * ∑ i, ∫ y, ‖f i y‖ ^ 2 ∂μ := by
  classical
  have hs (p : I × K) := double_cutoff_commutator_uniform μ (v p.2) (a j p.1 p.2) (b j p.1 p.2) χ η
    (ha j p.1 p.2) (hb j p.1 p.2) (hca j p.1 p.2) (hcb j p.1 p.2) hχ hcχ hη hcη
  choose C hC hbound using hs
  refine ⟨(Fintype.card (I × K) : ℝ) * ∑ p, C p, mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun p _ => hC p)), ?_⟩
  intro f hf hcf c hc
  let u (p : I × K) := doubleCutoffCommutator μ (kernel E μ c) (v p.2) (a j p.1 p.2) (b j p.1 p.2) χ η (f p.1)
  let U := ∑ i, ∫ y, ‖f i y‖ ^ 2 ∂μ
  have hU (i : I) : (∫ y, ‖f i y‖ ^ 2 ∂μ) ≤ U :=
    Finset.single_le_sum (f := fun i : I => ∫ y, ‖f i y‖ ^ 2 ∂μ)
      (fun i _ => integral_nonneg (fun y => sq_nonneg _)) (Finset.mem_univ i)
  have hu (p : I × K) : (∫ x, u p x ^ 2 ∂μ) ≤ C p * U := by
    have h := hbound p (f p.1) (hf p.1) (hcf p.1) c hc
    have ht : (∫ x, u p x ^ 2 ∂μ) ≤ C p * ∫ y, ‖f p.1 y‖ ^ 2 ∂μ := by
      simpa only [u, doubleCutoffCommutator, Real.norm_eq_abs, sq_abs] using h
    exact ht.trans (mul_le_mul_of_nonneg_left (hU p.1) (hC p))
  have hm (p : I × K) : AEStronglyMeasurable (u p) μ :=
    (continuous_doubleCutoffCommutator μ _ _ _ _ _ _ _ ((kernel_contDiff E μ c).of_le (by simp))
      (kernel_compact E μ c hc.ne') (ha j p.1 p.2).continuous (hb j p.1 p.2) hχ.continuous hη (hf p.1)).aestronglyMeasurable
  have hi (p : I × K) : Integrable (fun x => u p x ^ 2) μ :=
    integrable_square_doubleCutoffCommutator μ _ _ _ _ _ _ _ ((kernel_contDiff E μ c).of_le (by simp))
      (kernel_compact E μ c hc.ne') (ha j p.1 p.2).continuous (hb j p.1 p.2) hχ.continuous hη hcη (hf p.1)
  have hsum := FiniteIntegralSquare.integral_sum_square_le Finset.univ u (fun p _ => hm p) (fun p _ => hi p)
  have hsum' : (∫ x, (∑ p : I × K, u p x) ^ 2 ∂μ) ≤
      ((Fintype.card (I × K) : ℝ) * ∑ p, C p) * U := by
    calc
      _ ≤ (Fintype.card (I × K) : ℝ) * ∑ p, ∫ x, u p x ^ 2 ∂μ := by simpa using hsum
      _ ≤ (Fintype.card (I × K) : ℝ) * ∑ p, C p * U :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => hu p)) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have he (x : E) : matrixFirstOrder v a b (fun i y => η y * scalarConvolution μ (kernel E μ c) (fun z => χ z * f i z) y) j x -
      η x * scalarConvolution μ (kernel E μ c) (fun z => χ z * matrixFirstOrder v a b f j z) x = ∑ p : I × K, u p x := by
    rw [matrix_double_cutoff_commutator μ _ χ η v a b f (kernel_contDiff E μ c).continuous
      (fun j i k => (ha j i k).continuous) hb hχ.continuous hcχ hf]
    simp only [Fintype.sum_prod_type, u, doubleCutoffCommutator]
  simp_rw [he, Real.norm_eq_abs, sq_abs]
  simpa only [U, Real.norm_eq_abs, sq_abs] using hsum'

end TernaryPoly.CompactScalarMollifier
