module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section


/-! Local smoothness of the actual weighted coordinate adjoint on its true open domain. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- Differentiation of the metric-weighted factor is smooth on the actual open chart. -/
theorem contDiffOn_transposeOrder {U : Set E} (hU : IsOpen U) {a b g : E → ℝ} (v : E)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (transposeOrder v a b g) U :=
  (hb.mul hg).sub (((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp (ha.mul hg)).2.clm_apply
    contDiffOn_const)

omit [Fintype I] in
theorem contDiffOn_matrixTranspose {U : Set E} (hU : IsOpen U)
    (v : K → E) (a b : J → I → K → E →ℝ) (g : J → E → ℝ)
    (ha : ∀ j i k, ContDiffOn ℝ ∞ (a j i k) U)
    (hb : ∀ j i k, ContDiffOn ℝ ∞ (b j i k) U)
    (hg : ∀ j, ContDiffOn ℝ ∞ (g j) U) (i : I) :
    ContDiffOn ℝ ∞ (matrixTranspose v a b g i) U :=
  ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun k _ =>
    contDiffOn_transposeOrder hU (v k) (ha j i k) (hb j i k) (hg j)))

/-- Smoothness of the literal inverse-Gram adjoint requires metric data only on U. -/
theorem contDiffOn_weightedMatrixAdjoint [DecidableEq I] {U : Set E} (hU : IsOpen U)
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (hM : ∀ i l, ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ i l) U)
    (hN : ∀ j l, ContDiffOn ℝ ∞ (fun x => N x j l) U)
    (v : K → E) (a b : J → I → K → E → ℝ) (g : J → E → ℝ)
    (ha : ∀ j i k, ContDiffOn ℝ ∞ (a j i k) U)
    (hb : ∀ j i k, ContDiffOn ℝ ∞ (b j i k) U)
    (hg : ∀ j, ContDiffOn ℝ ∞ (g j) U) (i : I) :
    ContDiffOn ℝ ∞ (weightedMatrixAdjoint M N v a b g i) U :=
  contDiffOn_metricDual hM (fun l => contDiffOn_matrixTranspose hU v a b (metricDual N g) ha hb
    (fun j => contDiffOn_metricDual hN hg j) l) i

end TernaryPoly.CompactCoordinateIntegration
