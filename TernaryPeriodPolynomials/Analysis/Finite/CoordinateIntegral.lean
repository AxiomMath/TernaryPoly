module

public import TernaryPeriodPolynomials.Analysis.Finite.CoordinateSquare
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section

/-! Integrating the exact finite-coordinate square estimates. -/
namespace TernaryPoly.FiniteCoordinateSquare
open MeasureTheory
variable {I F X : Type*} [Fintype I] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace X] {μ : Measure X}

theorem integral_square_le_coordinates (e : F ≃L[ℝ] (I → ℝ)) (z : X → F)
    (hz : Integrable (fun x => ‖z x‖ ^ 2) μ)
    (hc : ∀ i, Integrable (fun x => ‖e (z x) i‖ ^ 2) μ) :
    ∫ x, ‖z x‖ ^ 2 ∂μ ≤ ‖e.symm.toContinuousLinearMap‖ ^ 2 *
      ∑ i, ∫ x, ‖e (z x) i‖ ^ 2 ∂μ := by
  have hs : Integrable (fun x => ∑ i, ‖e (z x) i‖ ^ 2) μ :=
    integrable_finsetSum _ (fun i _ => hc i)
  calc
    _ ≤ ∫ x, ‖e.symm.toContinuousLinearMap‖ ^ 2 * ∑ i, ‖e (z x) i‖ ^ 2 ∂μ :=
      integral_mono hz (hs.const_mul _) (fun x => square_le_coordinates e (z x))
    _ = _ := by rw [integral_const_mul, integral_finsetSum _ (fun i _ => hc i)]

theorem integral_coordinates_le_square (e : F ≃L[ℝ] (I → ℝ)) (z : X → F)
    (hz : Integrable (fun x => ‖z x‖ ^ 2) μ)
    (hc : ∀ i, Integrable (fun x => ‖e (z x) i‖ ^ 2) μ) :
    ∑ i, ∫ x, ‖e (z x) i‖ ^ 2 ∂μ ≤
      (Fintype.card I : ℝ) * ‖e.toContinuousLinearMap‖ ^ 2 * ∫ x, ‖z x‖ ^ 2 ∂μ := by
  rw [← integral_finsetSum _ (fun i _ => hc i), ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun i _ => hc i)) (hz.const_mul _)
    (fun x => coordinates_le_square e (z x))

end TernaryPoly.FiniteCoordinateSquare
