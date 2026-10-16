module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.OperatorRegularity

@[expose] public section


/-! Local positive Gram matrices suffice for compact coordinate integration by parts. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory Set Filter
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothness on an open neighborhood of the closed support gives global smoothness. -/
theorem contDiff_of_tsupport_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} {r : WithTop ℕ∞}
    (hf : ContDiffOn ℝ r f U) (hs : tsupport f ⊆ U) : ContDiff ℝ r f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hf x hx).contDiffAt (hU.mem_nhds hx)
  · exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hs ht)))

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- A varying metric dual remains smooth on its given open domain. -/
theorem contDiffOn_metricDual {M : E → Matrix I I ℝ} {f : I → E → ℝ}
    {U : Set E} {r : WithTop ℕ∞} (hM : ∀ i l, ContDiffOn ℝ r (fun x => M x i l) U)
    (hf : ∀ i, ContDiffOn ℝ r (f i) U) (i : I) : ContDiffOn ℝ r (metricDual M f i) U := by
  unfold metricDual Matrix.mulVec dotProduct
  exact ContDiffOn.sum (fun l _ => (hM i l).mul (hf l))

omit [NormedSpace ℝ E] in
/-- The metric dual creates no new support, even where metric coefficients are arbitrary. -/
theorem tsupport_metricDual_subset (M : E → Matrix I I ℝ) (f : I → E → ℝ)
    {U : Set E} (hU : IsClosed U) (hs : ∀ i, tsupport (f i) ⊆ U) (i : I) :
    tsupport (metricDual M f i) ⊆ U := by
  apply closure_minimal _ hU
  intro x hx
  by_contra hxu
  apply hx
  change ∑ l, M x i l * f l x = 0
  apply Finset.sum_eq_zero
  intro l _
  rw [image_eq_zero_of_notMem_tsupport (fun h => hxu (hs l h)), mul_zero]

omit [NormedSpace ℝ E] in
/-- Support of a finite metric dual lies in the union of the closed supports of its components. -/
theorem tsupport_metricDual_union (M : E → Matrix I I ℝ) (f : I → E → ℝ) (i : I) :
    tsupport (metricDual M f i) ⊆ ⋃ l, tsupport (f l) :=
  tsupport_metricDual_subset M f (isClosed_iUnion_of_finite (fun l => isClosed_tsupport (f l)))
    (fun l => subset_iUnion (fun j => tsupport (f j)) l) i

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Genuine local coordinate formula: metric smoothness/invertibility is needed only on U. -/
theorem integral_weightedMatrixAdjoint_on [DecidableEq I] [DecidableEq J]
    {U : Set E} (hU : IsOpen U) (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (hM : ∀ x ∈ U, IsUnit (M x).det) (hN : ∀ j l, ContDiffOn ℝ 1 (fun x => N x j l) U)
    (v : K → E) (a b : J → I → K → E → ℝ) (f : I → E → ℝ) (g : J → E → ℝ)
    (ha : ∀ j i k, ContDiff ℝ 1 (a j i k)) (hb : ∀ j i k, Continuous (b j i k))
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hg : ∀ j, ContDiffOn ℝ 1 (g j) U)
    (hc : ∀ i, HasCompactSupport (f i))
    (hsf : ∀ i, tsupport (f i) ⊆ U) (hsg : ∀ j, tsupport (g j) ⊆ U) :
    ∫ x, weightedPairing N (matrixFirstOrder v a b f) g x ∂μ =
      ∫ x, weightedPairing M f (weightedMatrixAdjoint M N v a b g) x ∂μ := by
  have hdual j : ContDiff ℝ 1 (metricDual N g j) :=
    contDiff_of_tsupport_subset hU (contDiffOn_metricDual hN hg j)
      ((tsupport_metricDual_union N g j).trans (iUnion_subset hsg))
  have heq := integral_matrixFirstOrder (μ := μ) v a b f (metricDual N g) ha hb hf hdual hc
  refine heq.trans ?_
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  unfold weightedPairing
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ U
  · change f i x * _ = f i x * ((M x).mulVec ((M x)⁻¹.mulVec
        (fun l => matrixTranspose v a b (metricDual N g) l x))) i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hM x hx), Matrix.one_mulVec]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsf i ht)), zero_mul, zero_mul]

end TernaryPoly.CompactCoordinateIntegration
