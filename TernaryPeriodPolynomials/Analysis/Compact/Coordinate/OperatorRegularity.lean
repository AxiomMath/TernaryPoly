module

public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.MatrixAdjoint

@[expose] public section


/-! The explicit coordinate differential and weighted formal adjoint preserve smooth compact fields. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth first-order scalar expressions are smooth. -/
theorem contDiff_firstOrder {a b f : E → ℝ} (v : E)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (firstOrder v a b f) :=
  (ha.mul ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const)).add (hb.mul hf)

/-- The actual transpose divergence is smooth, including derivatives of its coefficients. -/
theorem contDiff_transposeOrder {a b g : E → ℝ} (v : E)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (transposeOrder v a b g) :=
  (hb.mul hg).sub ((contDiff_infty_iff_fderiv.mp (ha.mul hg)).2.clm_apply contDiff_const)

omit [NormedSpace ℝ E] in
/-- A finite sum of compactly supported scalar fields is compactly supported. -/
theorem compact_sum {ι : Type*} [Fintype ι] (f : ι → E → ℝ)
    (hf : ∀ i, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i, f i x) := by
  have he : (fun x => ∑ i, f i x) = (∑ i, f i) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact HasCompactSupport.finset_sum (fun i _ => hf i)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

omit [Fintype J] in
theorem contDiff_matrixFirstOrder (v : K → E) (a b : J → I → K → E → ℝ)
    (f : I → E → ℝ) (ha : ∀ j i k, ContDiff ℝ ∞ (a j i k))
    (hb : ∀ j i k, ContDiff ℝ ∞ (b j i k)) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (j : J) :
    ContDiff ℝ ∞ (matrixFirstOrder v a b f j) :=
  ContDiff.sum (fun i _ => ContDiff.sum (fun k _ =>
    contDiff_firstOrder (v k) (ha j i k) (hb j i k) (hf i)))

omit [Fintype I] in
theorem contDiff_matrixTranspose (v : K → E) (a b : J → I → K → E → ℝ)
    (g : J → E → ℝ) (ha : ∀ j i k, ContDiff ℝ ∞ (a j i k))
    (hb : ∀ j i k, ContDiff ℝ ∞ (b j i k)) (hg : ∀ j, ContDiff ℝ ∞ (g j)) (i : I) :
    ContDiff ℝ ∞ (matrixTranspose v a b g i) :=
  ContDiff.sum (fun j _ => ContDiff.sum (fun k _ =>
    contDiff_transposeOrder (v k) (ha j i k) (hb j i k) (hg j)))

omit [Fintype J] in
theorem compact_matrixFirstOrder (v : K → E) (a b : J → I → K → E → ℝ)
    (f : I → E → ℝ) (hc : ∀ i, HasCompactSupport (f i)) (j : J) :
    HasCompactSupport (matrixFirstOrder v a b f j) :=
  compact_sum _ (fun i => compact_sum _ (fun k => compact_firstOrder (v k) _ _ (hc i)))

omit [Fintype I] in
theorem compact_matrixTranspose (v : K → E) (a b : J → I → K → E → ℝ)
    (g : J → E → ℝ) (hc : ∀ j, HasCompactSupport (g j)) (i : I) :
    HasCompactSupport (matrixTranspose v a b g i) :=
  compact_sum _ (fun j => compact_sum _ (fun k => compact_transposeOrder (v k) _ _ (hc j)))

omit [NormedSpace ℝ E] in
theorem compact_metricDual (M : E → Matrix I I ℝ) (f : I → E → ℝ)
    (hc : ∀ i, HasCompactSupport (f i)) (i : I) : HasCompactSupport (metricDual M f i) :=
  compact_sum _ (fun l => (hc l).mul_left)

/-- Smoothness of the actual inverse-metric formal adjoint; inverse Gram smoothness is explicit. -/
theorem contDiff_weightedMatrixAdjoint [DecidableEq I]
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (hM : ∀ i l, ContDiff ℝ ∞ (fun x => (M x)⁻¹ i l))
    (hN : ∀ j l, ContDiff ℝ ∞ (fun x => N x j l))
    (v : K → E) (a b : J → I → K → E → ℝ) (g : J → E → ℝ)
    (ha : ∀ j i k, ContDiff ℝ ∞ (a j i k)) (hb : ∀ j i k, ContDiff ℝ ∞ (b j i k))
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (i : I) :
    ContDiff ℝ ∞ (weightedMatrixAdjoint M N v a b g i) :=
  contDiff_metricDual hM (fun l => contDiff_matrixTranspose v a b (metricDual N g) ha hb
    (fun j => contDiff_metricDual hN hg j) l) i

/-- Compact support needs no boundedness assumption on metric coefficients or their inverses. -/
theorem compact_weightedMatrixAdjoint [DecidableEq I]
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a b : J → I → K → E →ℝ) (g : J → E → ℝ)
    (hc : ∀ j, HasCompactSupport (g j)) (i : I) :
    HasCompactSupport (weightedMatrixAdjoint M N v a b g i) :=
  compact_metricDual _ _ (fun l => compact_matrixTranspose v a b (metricDual N g)
    (fun j => compact_metricDual N g hc j) l) i

end TernaryPoly.CompactCoordinateIntegration
