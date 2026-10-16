module

public import TernaryPeriodPolynomials.DifferentialForm.WeightedSquare
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

@[expose] public section


/-! Actual compact metric comparison transports square-integral convergence. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open MeasureTheory Filter PolynomialFormMetric SymmetricSpaceCharts
open scoped ContDiff

theorem compact_weighted_square_tendsto {ι : Type*} {l : Filter ι} (n k : ℕ)
    (K : Set Coordinates) (hK : IsCompact K) (hKpos : K ⊆ positiveCoordinates)
    (w : ι → Coordinates → FormValue n k)
    (hw : ∀ᶠ i in l, ContDiff ℝ ∞ (w i) ∧ HasCompactSupport (w i) ∧ tsupport (w i) ⊆ K)
    (ht : Tendsto (fun i => ∫ x, ‖w i x‖^2) l (nhds 0)) :
    Tendsto (fun i => ∫ x, weightedSquare n k (w i) x) l (nhds 0) := by
  obtain ⟨d,C,hd,_,hb⟩ := compact_integral_weighted_bounds n k hK hKpos
  have hlo : ∀ᶠ i in l, 0 ≤ ∫ x, weightedSquare n k (w i) x := by
    filter_upwards [hw] with i hi
    exact (mul_nonneg hd.le (integral_nonneg (fun x => sq_nonneg _))).trans (hb (w i) hi.1 hi.2.1 hi.2.2).1
  have hhi : ∀ᶠ i in l, (∫ x, weightedSquare n k (w i) x) ≤ C * ∫ x, ‖w i x‖^2 := by
    filter_upwards [hw] with i hi
    exact (hb (w i) hi.1 hi.2.1 hi.2.2).2
  exact squeeze_zero' hlo hhi (by simpa only [mul_zero] using ht.const_mul C)

end TernaryPoly.PolynomialFormCoordinates
