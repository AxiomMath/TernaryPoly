module

public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.FirstOrderExpansion
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalRegularity

@[expose] public section


/-! Smoothness of every explicit first-order coefficient of the actual weighted adjoint. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Set
open scoped ContDiff
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]

omit [Fintype J] [Fintype K] in
theorem contDiffOn_weightedFirstCoefficient {U : Set E}
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ) (a : J → I → K → E → ℝ)
    (hM : ∀ i l, ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ i l) U)
    (hN : ∀ j t, ContDiffOn ℝ ∞ (fun x => N x j t) U)
    (ha : ∀ j l k, ContDiffOn ℝ ∞ (a j l k) U) (i : I) (t : J) (l : I) (j : J) (k : K) :
    ContDiffOn ℝ ∞ (weightedFirstCoefficient M N a i t l j k) U :=
  (hM i l).mul ((ha j l k).neg.mul (hN j t))

omit [Fintype J] [Fintype K] in
theorem contDiffOn_weightedZeroCoefficient {U : Set E} (hU : IsOpen U)
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ) (v : K → E) (a b : J → I → K → E → ℝ)
    (hM : ∀ i l, ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ i l) U)
    (hN : ∀ j t, ContDiffOn ℝ ∞ (fun x => N x j t) U)
    (ha : ∀ j l k, ContDiffOn ℝ ∞ (a j l k) U)
    (hb : ∀ j l k, ContDiffOn ℝ ∞ (b j l k) U) (i : I) (t : J) (l : I) (j : J) (k : K) :
    ContDiffOn ℝ ∞ (weightedZeroCoefficient M N v a b i t l j k) U := by
  have hda : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (a j l k) x (v k)) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp (ha j l k)).2.clm_apply contDiffOn_const
  have hdN : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => N y j t) x (v k)) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp (hN j t)).2.clm_apply contDiffOn_const
  exact (hM i l).mul (((hb j l k).mul (hN j t)).sub (hda.mul (hN j t)) |>.sub ((ha j l k).mul hdN))

end TernaryPoly.CompactCoordinateIntegration
