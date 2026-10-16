module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Quantitative compactly supported Lipschitz cutoffs on a proper metric space. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Metric Filter
open scoped Topology NNReal
variable {X : Type*} [MetricSpace X]

/-- A unit-height plateau on radius `r`, vanishing outside radius `2r`. -/
def metricCutoff (x₀ : X) (r : ℝ) (x : X) : ℝ := max 0 (min 1 (2 - r⁻¹ * dist x₀ x))

theorem metricCutoff_mem_Icc (x₀ : X) (r : ℝ) (x : X) : metricCutoff x₀ r x ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem metricCutoff_eq_one (x₀ : X) {r : ℝ} (hr : 0 < r) {x : X} (hx : dist x₀ x ≤ r) :
    metricCutoff x₀ r x = 1 := by
  have h : r⁻¹ * dist x₀ x ≤ 1 := by
    calc
      _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hr.le)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  simp only [metricCutoff, min_eq_left (by linarith : 1 ≤ 2 - r⁻¹ * dist x₀ x)]
  norm_num

theorem metricCutoff_eq_zero (x₀ : X) {r : ℝ} (hr : 0 < r) {x : X} (hx : 2 * r ≤ dist x₀ x) :
    metricCutoff x₀ r x = 0 := by
  have h : 2 ≤ r⁻¹ * dist x₀ x := by
    calc
      2 = r⁻¹ * (2 * r) := by field_simp
      _ ≤ r⁻¹ * dist x₀ x := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hr.le)
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem lipschitzWith_metricCutoff (x₀ : X) {r : ℝ} (hr : 0 < r) :
    LipschitzWith ⟨r⁻¹, inv_nonneg.mpr hr.le⟩ (metricCutoff x₀ r) := by
  have h : LipschitzWith ⟨r⁻¹, inv_nonneg.mpr hr.le⟩ (fun x => 2 - r⁻¹ * dist x₀ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (2 - r⁻¹ * dist x₀ x) (2 - r⁻¹ * dist x₀ y) ≤ r⁻¹ * dist x y
    rw [dist_sub_left, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hr.le)]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (LipschitzWith.dist_right x₀).dist_le_mul x y) (inv_nonneg.mpr hr.le)
  exact (h.const_min 1).const_max 0

theorem metricCutoff_hasCompactSupport [ProperSpace X] (x₀ : X) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (metricCutoff x₀ r) := by
  apply HasCompactSupport.intro (K := closedBall x₀ (2 * r)) (isCompact_closedBall _ _)
  intro x hx
  apply metricCutoff_eq_zero x₀ hr
  have h : ¬ dist x x₀ ≤ 2 * r := hx
  rw [dist_comm] at h
  exact (lt_of_not_ge h).le

/-- Each point strictly inside the inner ball has a neighborhood on which the cutoff is one. -/
theorem metricCutoff_eventually_one (x₀ : X) {r : ℝ} (hr : 0 < r) {x : X}
    (hx : dist x₀ x < r) : metricCutoff x₀ r =ᶠ[𝓝 x] 1 := by
  have hx' : x ∈ ball x₀ r := by simpa only [mem_ball, dist_comm] using hx
  filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
  apply metricCutoff_eq_one x₀ hr
  exact (show dist x₀ y < r by simpa only [mem_ball, dist_comm] using hy).le

/-- The radius-j sequence equals one eventually on every compact subset. -/
theorem metricCutoff_eventually_one_on_compact (x₀ : X) {K : Set X} (hK : IsCompact K) :
    ∀ᶠ j : ℕ in atTop, ∀ x ∈ K, metricCutoff x₀ ((j : ℝ) + 1) x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball x₀
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with j hj x hx
  apply metricCutoff_eq_one x₀ (by positivity)
  have h : dist x₀ x < R := by simpa only [mem_ball, dist_comm] using hR hx
  have hcast : (N : ℝ) ≤ j := by exact_mod_cast hj
  linarith

end TernaryPoly.PolynomialFormConnection
