module

public import TernaryPeriodPolynomials.Topology.Supported.InwardModel

@[expose] public section


noncomputable section
namespace TernaryPoly.SupportedDownward
open scoped unitInterval
open Metric
open SupportedInward (HalfLine Model)
variable {E : Type*} [MetricSpace E]

/-- A radial cutoff equal to one on the radius-r ball and zero outside radius 2r. -/
def cutoff (z : Model E) (r : ℝ) (y : Model E) : ℝ :=
  min 1 (max 0 (2 - dist y z / r))

theorem cutoff_nonneg (z : Model E) (r : ℝ) (y : Model E) : 0 ≤ cutoff z r y :=
  le_min zero_le_one (le_max_left _ _)

theorem cutoff_le_one (z : Model E) (r : ℝ) (y : Model E) : cutoff z r y ≤ 1 :=
  min_le_left _ _

theorem cutoff_continuous (z : Model E) (r : ℝ) : Continuous (cutoff z r) := by
  unfold cutoff
  fun_prop

theorem cutoff_one (z : Model E) (r : ℝ) (hr : 0 < r) (y : Model E)
    (hy : dist y z ≤ r) : cutoff z r y = 1 := by
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  have h := (div_le_one hr).mpr hy
  linarith

theorem cutoff_zero (z : Model E) (r : ℝ) (hr : 0 < r) (y : Model E)
    (hy : 2 * r ≤ dist y z) : cutoff z r y = 0 := by
  have h := (le_div_iff₀ hr).mpr hy
  change min 1 (max 0 (2 - dist y z / r)) = 0
  rw [max_eq_left (by linarith : 2 - dist y z / r ≤ 0), min_eq_right zero_le_one]

theorem factor_nonneg (z : Model E) (r : ℝ) (t : I) (y : Model E) :
    0 ≤ 1 - t.val * cutoff z r y := by
  have h := mul_le_mul_of_nonneg_right t.property.2 (cutoff_nonneg z r y)
  nlinarith [cutoff_le_one z r y]

theorem factor_le_one (z : Model E) (r : ℝ) (t : I) (y : Model E) :
    1 - t.val * cutoff z r y ≤ 1 :=
  sub_le_self _ (mul_nonneg t.property.1 (cutoff_nonneg z r y))

/-- The supported deformation decreases height by the radial cutoff. -/
def down (z : Model E) (r : ℝ) (t : I) (y : Model E) : Model E :=
  (y.1, ⟨(1 - t.val * cutoff z r y) * y.2.val,
    mul_nonneg (factor_nonneg z r t y) y.2.property⟩)

@[simp] theorem down_height (z : Model E) (r : ℝ) (t : I) (y : Model E) :
    (down z r t y).2.val = (1 - t.val * cutoff z r y) * y.2.val := rfl

theorem down_continuous (z : Model E) (r : ℝ) :
    Continuous (fun p : I × Model E => down z r p.1 p.2) := by
  unfold down
  have hc := cutoff_continuous z r
  fun_prop

@[simp] theorem down_zero (z : Model E) (r : ℝ) (y : Model E) : down z r 0 y = y := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  simp [down]

theorem down_eq (z : Model E) (r : ℝ) (t : I) (y : Model E)
    (hy : cutoff z r y = 0) : down z r t y = y := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  simp [down, hy]

theorem down_boundary (z : Model E) (r : ℝ) (t : I) (y : Model E)
    (hy : y.2.val = 0) : down z r t y = y := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  simp [down, hy]

theorem down_height_le (z : Model E) (r : ℝ) (t : I) (y : Model E) :
    (down z r t y).2.val ≤ y.2.val := by
  exact (mul_le_mul_of_nonneg_right (factor_le_one z r t y) y.2.property).trans_eq
    (one_mul _)

/-- Scaling height down does not increase distance from a boundary-centered point. -/
theorem down_dist_le (z : Model E) (hz : z.2.val = 0) (r : ℝ) (t : I) (y : Model E) :
    dist (down z r t y) z ≤ dist y z := by
  rw [Prod.dist_eq, Prod.dist_eq]
  apply max_le_max (le_refl _)
  simp only [Subtype.dist_eq, Real.dist_eq, hz, sub_zero]
  rw [abs_of_nonneg (down z r t y).2.property, abs_of_nonneg y.2.property]
  exact down_height_le z r t y

/-- Any region containing the supporting ball is preserved by the downward deformation. -/
theorem down_mem (z : Model E) (hz : z.2.val = 0) (r : ℝ) (hr : 0 < r)
    (V : Set (Model E)) (hball : closedBall z (2 * r) ⊆ V)
    (t : I) (y : Model E) (hy : y ∈ V) : down z r t y ∈ V := by
  by_cases h : cutoff z r y = 0
  · rwa [down_eq z r t y h]
  · have hd : dist y z < 2 * r := by
      by_contra hn
      exact h (cutoff_zero z r hr y (le_of_not_gt hn))
    exact hball ((down_dist_le z hz r t y).trans hd.le)

/-- At time one the entire radius-r core is on the boundary. -/
theorem down_one_height (z : Model E) (r : ℝ) (hr : 0 < r) (y : Model E)
    (hy : dist y z ≤ r) : (down z r 1 y).2.val = 0 := by
  simp [down_height, cutoff_one z r hr y hy]

end TernaryPoly.SupportedDownward
