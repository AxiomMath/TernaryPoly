module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.ChartPartitionAgreement
public import TernaryPeriodPolynomials.DifferentialForm.WeakFiniteReconstruction

@[expose] public section


/-! Actual Hilbert chart limits for a fixed genuine finite compact partition. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set PolynomialFormHilbert PolynomialFormConnection
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff
attribute [local instance] cutoffHilbertModule

theorem CompactChartPartitionData.exists_hilbert_limits {K : Set OrbitSpace}
    (p : CompactChartPartitionData K) (n k : ℕ) :
    ∃ L : p.charts → Hilbert n k →L[ℝ] Hilbert n k,
      (∀ (i : p.charts) (a : Core n k), L i (inclusion n k a) = inclusion n k
        (doubleChartCutoff n k i.val (p.cutoff i).inner (p.cutoff i).outer
          (p.cutoff i).inner_smooth (p.cutoff i).outer_smooth
          (p.cutoff i).outer_compact (p.cutoff i).outer_support a.val)) ∧
      (∀ i : p.charts, HasStrongHilbertChartLimit n k i.val (p.cutoff i).inner (p.cutoff i).outer
        (p.cutoff i).inner_smooth (p.cutoff i).inner_compact (p.cutoff i).inner_support
        (p.cutoff i).outer_smooth (p.cutoff i).outer_compact (p.cutoff i).outer_support (L i)) ∧
      ∀ u : Hilbert n k, HasWeakSupportIn n k K u → ∑ i, L i u = u := by
  classical
  have hlim (i : p.charts) := exists_hilbertChartLimit n k i.val (p.cutoff i).inner
    (p.cutoff i).outer (p.cutoff i).inner_smooth (p.cutoff i).inner_compact
    (p.cutoff i).inner_support (p.cutoff i).outer_smooth (p.cutoff i).outer_compact
    (p.cutoff i).outer_support
  choose L hL hconv using hlim
  refine ⟨L, hL, hconv, ?_⟩
  intro u hu
  apply finite_scalar_reconstruction_of_weakSupport n k p.scalar p.smooth L _ K
    p.neighborhood p.neighborhood_open p.subset_neighborhood p.sum_one u hu
  intro i a
  exact (hL i a).trans (congrArg (inclusion n k) (p.core_agreement n k i a))

end TernaryPoly.PolynomialFormCoordinates
