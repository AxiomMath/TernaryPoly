module

public import TernaryPeriodPolynomials.Analysis.Compact.FirstOrderCutoffConvolution
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FormalAdjoint
public import TernaryPeriodPolynomials.Analysis.Finite.IntegralSquare
public import Mathlib.Tactic.Choose

@[expose] public section


/-! Every finite first-order expression after fixed-scale cutoff convolution is L2-bounded. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype I] [Fintype K]

theorem exists_matrix_cutoff_convolution_bound (v : K → E) (κ η : E → ℝ)
    (a b : J → I → K → E → ℝ) (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (ha : ∀ j i d, Continuous (a j i d)) (hb : ∀ j i d, Continuous (b j i d)) (j : J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : I → E → ℝ, (∀ i, Continuous (f i)) →
      (∀ i, HasCompactSupport (f i)) →
      ∫ x, ‖matrixFirstOrder v a b (fun i y => η y * scalarConvolution μ κ (f i) y) j x‖^2 ∂μ ≤
        C * ∑ i, ∫ x, ‖f i x‖^2 ∂μ := by
  classical
  have hs (p : I × K) := exists_firstOrder_cutoff_convolution_bound μ (v p.2) κ
    (a j p.1 p.2) (b j p.1 p.2) η hκ hcκ (ha j p.1 p.2) (hb j p.1 p.2) hη hcη
  choose C hC hbound using hs
  refine ⟨(Fintype.card (I × K) : ℝ) * ∑ p, C p,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun p _ => hC p)), ?_⟩
  intro f hf hcf
  let z (i : I) (x : E) := η x * scalarConvolution μ κ (f i) x
  let u (p : I × K) := firstOrder (v p.2) (a j p.1 p.2) (b j p.1 p.2) (z p.1)
  let U := ∑ i, ∫ x, ‖f i x‖^2 ∂μ
  have hz i : ContDiff ℝ 1 (z i) := hη.mul (contDiff_scalarConvolution μ κ (f i) hκ hcκ (hf i))
  have hcz i : HasCompactSupport (z i) := hcη.mul_right
  have hu p : Continuous (u p) := continuous_firstOrder (v p.2) (ha j p.1 p.2) (hb j p.1 p.2) (hz p.1)
  have hcu p : HasCompactSupport (u p) := compact_firstOrder (v p.2) (a j p.1 p.2) (b j p.1 p.2) (hcz p.1)
  have hi p : Integrable (fun x => u p x ^2) μ :=
    ((hu p).pow 2).integrable_of_hasCompactSupport (by simpa only [pow_two] using (hcu p).mul_right)
  have hU i : (∫ x, ‖f i x‖^2 ∂μ) ≤ U :=
    Finset.single_le_sum (f := fun i : I => ∫ x, ‖f i x‖^2 ∂μ)
      (fun i _ => integral_nonneg (fun x => sq_nonneg _)) (Finset.mem_univ i)
  have hbnd p : (∫ x, u p x ^2 ∂μ) ≤ C p * U := by
    have h := hbound p (f p.1) (hf p.1) (hcf p.1)
    have h' : (∫ x, u p x ^2 ∂μ) ≤ C p * ∫ x, ‖f p.1 x‖^2 ∂μ := by
      simpa only [u, z, Real.norm_eq_abs, sq_abs] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (hU p.1) (hC p))
  have hsum := FiniteIntegralSquare.integral_sum_square_le Finset.univ u
    (fun p _ => (hu p).aestronglyMeasurable) (fun p _ => hi p)
  have he (x : E) : matrixFirstOrder v a b z j x = ∑ p : I × K, u p x := by
    simp only [matrixFirstOrder, Fintype.sum_prod_type, u]
  simp_rw [show (fun i y => η y * scalarConvolution μ κ (f i) y) = z from rfl, he, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (Fintype.card (I × K) : ℝ) * ∑ p, ∫ x, u p x ^2 ∂μ := by simpa using hsum
    _ ≤ (Fintype.card (I × K) : ℝ) * ∑ p, C p * U :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => hbnd p)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; simp only [U, Real.norm_eq_abs, sq_abs]; ring

end TernaryPoly.CompactCoordinateIntegration
