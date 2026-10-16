module

public import TernaryPeriodPolynomials.Topology.InwardHomotopyBasic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section


noncomputable section
namespace TernaryPoly.SupportedInward
open scoped unitInterval
open Metric

abbrev HalfLine := {s : ℝ // 0≤s}
abbrev Model (E : Type*) := E × HalfLine

instance halfLineProper : ProperSpace HalfLine :=
  ProperSpace.of_isClosed (isClosed_le continuous_const continuous_id)

variable {E : Type*} [MetricSpace E]

/-- A nonnegative radial bump supported in the closed radius-r ball. -/
def bump (z : Model E) (r : ℝ) (y : Model E) : ℝ := max 0 (r-dist y z)

theorem bump_nonneg (z : Model E) (r : ℝ) (y : Model E) : 0≤bump z r y := le_max_left _ _

theorem bump_le (z : Model E) (r : ℝ) (hr : 0≤r) (y : Model E) : bump z r y≤r :=
  max_le hr (sub_le_self _ dist_nonneg)

theorem bump_zero (z : Model E) (r : ℝ) (y : Model E) (hy : r≤dist y z) : bump z r y=0 :=
  max_eq_left (sub_nonpos.mpr hy)

theorem bump_continuous (z : Model E) (r : ℝ) : Continuous (bump z r) := by
  unfold bump
  fun_prop

/-- Vertical displacement with parameter in the ordinary unit interval. -/
def push (z : Model E) (r : ℝ) (t : I) (y : Model E) : Model E :=
  (y.1,⟨y.2.val+t.val*bump z r y,
    add_nonneg y.2.property (mul_nonneg t.property.1 (bump_nonneg z r y))⟩)

@[simp] theorem push_height (z : Model E) (r : ℝ) (t : I) (y : Model E) :
    (push z r t y).2.val=y.2.val+t.val*bump z r y := rfl

theorem push_continuous (z : Model E) (r : ℝ) :
    Continuous (fun p : I × Model E => push z r p.1 p.2) := by
  unfold push
  have hb := bump_continuous z r
  fun_prop

@[simp] theorem push_zero (z : Model E) (r : ℝ) (y : Model E) : push z r 0 y=y := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  simp [push]

theorem push_eq (z : Model E) (r : ℝ) (t : I) (y : Model E)
    (hy : bump z r y=0) : push z r t y=y := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  simp [push,hy]

theorem push_height_mono (z : Model E) (r : ℝ) (t : I) (y : Model E) :
    y.2.val≤(push z r t y).2.val :=
  le_add_of_nonneg_right (mul_nonneg t.property.1 (bump_nonneg z r y))

theorem push_dist (z : Model E) (r : ℝ) (t : I) (y : Model E) :
    dist (push z r t y) y=t.val*bump z r y := by
  rw [Prod.dist_eq]
  simp only [push,dist_self,Subtype.dist_eq,Real.dist_eq]
  have ht : 0≤t.val*bump z r y := mul_nonneg t.property.1 (bump_nonneg z r y)
  rw [add_sub_cancel_left,abs_of_nonneg ht,max_eq_right ht]

/-- The supported push stays in any open chart target containing a twice-larger closed ball. -/
theorem push_mem (z : Model E) (r : ℝ) (hr : 0<r) (V : Set (Model E))
    (hball : closedBall z (2*r)⊆V) (t : I) (y : Model E) (hy : y∈V) :
    push z r t y∈V := by
  by_cases hb : bump z r y=0
  · rwa [push_eq z r t y hb]
  · have hdist : dist y z<r := by
      by_contra h
      exact hb (bump_zero z r y (le_of_not_gt h))
    have hmove : dist (push z r t y) y≤r := by
      rw [push_dist]
      exact (mul_le_mul_of_nonneg_right t.property.2 (bump_nonneg z r y)).trans
        (by simpa only [one_mul] using bump_le z r hr.le y)
    apply hball
    change dist (push z r t y) z≤2*r
    calc
      dist (push z r t y) z≤dist (push z r t y) y+dist y z := dist_triangle _ _ _
      _≤r+r := add_le_add hmove hdist.le
      _=2*r := by ring

/-- The center is strictly interior at time one. -/
theorem push_center_positive (z : Model E) (r : ℝ) (hr : 0<r) :
    0<(push z r 1 z).2.val := by
  change 0<z.2.val+1*bump z r z
  simp only [bump,dist_self,sub_zero,max_eq_right hr.le,one_mul]
  exact add_pos_of_nonneg_of_pos z.2.property hr

/-- A time-one endpoint remaining at height zero did not move. -/
theorem push_endpoint_fixed (z : Model E) (r : ℝ) (y : Model E)
    (hy : ¬0<(push z r 1 y).2.val) : push z r 1 y=y := by
  apply push_eq
  have he := le_of_not_gt hy
  change y.2.val+1*bump z r y≤0 at he
  rw [one_mul] at he
  have hb := bump_nonneg z r y
  have hh := y.2.property
  linarith

end TernaryPoly.SupportedInward
