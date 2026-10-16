module

public import Mathlib

@[expose] public section


/-!
# Sign algebra for the degree computation (L4)

Formalized by Claude Sonnet 5.5.

Pure real-number facts: the side sign `sg`, the determinant `dt2` on `ℝ²`, the Plücker relation, the core difference identity
`-sg(d(c₁,a)d(c₂,a)) + sg(d(c₁,b)d(c₂,b)) = sg(d(c₁,c₂)) (H_{a,b}(c₂) - H_{a,b}(c₁))` and the triangle identity
`sg(xy) + sg(x(x-y)) + sg(y(y-x)) = 1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeSign

/-- The side sign (`+1` on positive reals, `-1` otherwise; only used on nonzero reals). -/
def sg (r : ℝ) : ℝ := if 0 < r then 1 else -1

theorem sg_pos {r : ℝ} (h : 0 < r) : sg r = 1 := ite_eq_left h

theorem sg_neg_of_neg {r : ℝ} (h : r < 0) : sg r = -1 := ite_eq_right (not_lt.mpr h.le)

theorem sg_mul {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) : sg (r * s) = sg r * sg s := by
  rcases lt_or_gt_of_ne hr with h1 | h1 <;> rcases lt_or_gt_of_ne hs with h2 | h2
  · rw [sg_pos (mul_pos_of_neg_of_neg h1 h2), sg_neg_of_neg h1, sg_neg_of_neg h2]; norm_num
  · rw [sg_neg_of_neg (mul_neg_of_neg_of_pos h1 h2), sg_neg_of_neg h1, sg_pos h2]; norm_num
  · rw [sg_neg_of_neg (mul_neg_of_pos_of_neg h1 h2), sg_pos h1, sg_neg_of_neg h2]; norm_num
  · rw [sg_pos (mul_pos h1 h2), sg_pos h1, sg_pos h2]; norm_num

theorem sg_neg {r : ℝ} (hr : r ≠ 0) : sg (-r) = - sg r := by
  rcases lt_or_gt_of_ne hr with h | h
  · rw [sg_pos (neg_pos.mpr h), sg_neg_of_neg h]; norm_num
  · rw [sg_neg_of_neg (neg_neg_of_pos h), sg_pos h]

theorem sg_sq {r : ℝ} (hr : r ≠ 0) : sg (r * r) = 1 := sg_pos (mul_self_pos.mpr hr)

theorem sg_sq_eq {r : ℝ} (hr : r ≠ 0) : sg r * sg r = 1 := by
  rw [← sg_mul hr hr, sg_sq hr]

/-- Six-real core identity, from the Plücker relation `m n = p₁ q₂ - q₁ p₂`. -/
theorem core_abstract (m n p1 p2 q1 q2 : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (h1 : p1 ≠ 0) (h2 : p2 ≠ 0)
    (h3 : q1 ≠ 0) (h4 : q2 ≠ 0) (pl : m * n = p1 * q2 - q1 * p2) :
    -sg (p1 * p2) + sg (q1 * q2) = sg m * (-sg n * sg (p2 * q2) + sg n * sg (p1 * q1)) := by
  rw [sg_mul h1 h2, sg_mul h3 h4, sg_mul h2 h4, sg_mul h1 h3]
  rcases lt_or_gt_of_ne hm with a1 | a1 <;> rcases lt_or_gt_of_ne hn with a2 | a2 <;>
  rcases lt_or_gt_of_ne h1 with a3 | a3 <;> rcases lt_or_gt_of_ne h2 with a4 | a4 <;>
  rcases lt_or_gt_of_ne h3 with a5 | a5 <;> rcases lt_or_gt_of_ne h4 with a6 | a6 <;>
  simp only [sg_pos, sg_neg_of_neg, a1, a2, a3, a4, a5, a6] <;> norm_num <;> nlinarith [pl]

/-- The triangle identity: for `x, y, x - y ≠ 0`, `sg(xy) + sg(x(x-y)) + sg(y(y-x)) = 1`. -/
theorem triangle_sum (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x - y ≠ 0) :
    sg (x * y) + sg (x * (x - y)) + sg (y * (y - x)) = 1 := by
  have hyx : y - x ≠ 0 := by intro h; apply hxy; linarith
  rw [sg_mul hx hy, sg_mul hx hxy, sg_mul hy hyx]
  rcases lt_or_gt_of_ne hx with a1 | a1 <;> rcases lt_or_gt_of_ne hy with a2 | a2 <;>
  rcases lt_or_gt_of_ne hxy with a3 | a3 <;>
  have a4 : y - x ≠ 0 := hyx <;>
  simp only [sg_pos, sg_neg_of_neg, a1, a2, a3] <;>
  (try rw [sg_pos (by linarith : (0:ℝ) < y - x)]) <;> (try rw [sg_neg_of_neg (by linarith : y - x < 0)]) <;>
  norm_num <;> linarith

/-- 2-dimensional determinant of real vectors. -/
def dt2 (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

theorem dt2_swap (u v : Fin 2 → ℝ) : dt2 v u = - dt2 u v := by simp [dt2]; ring

/-- The Plücker relation. -/
theorem plucker (c1 c2 a b : Fin 2 → ℝ) :
    dt2 c1 c2 * dt2 a b = dt2 c1 a * dt2 c2 b - dt2 c1 b * dt2 c2 a := by
  simp [dt2]; ring

/-- The side function `H_{a,b}` on a vector. -/
def Hv (a b c : Fin 2 → ℝ) : ℝ := - sg (dt2 a b) * sg (dt2 c a * dt2 c b)

/-- **The core difference identity** for two independent vectors `c₁, c₂` and two reference vectors `a, b`
(all relevant determinants nonzero). -/
theorem core (c1 c2 a b : Fin 2 → ℝ) (hm : dt2 c1 c2 ≠ 0) (hn : dt2 a b ≠ 0)
    (h1 : dt2 c1 a ≠ 0) (h2 : dt2 c2 a ≠ 0) (h3 : dt2 c1 b ≠ 0) (h4 : dt2 c2 b ≠ 0) :
    -sg (dt2 c1 a * dt2 c2 a) + sg (dt2 c1 b * dt2 c2 b) =
      sg (dt2 c1 c2) * (Hv a b c2 - Hv a b c1) := by
  have := core_abstract (dt2 c1 c2) (dt2 a b) (dt2 c1 a) (dt2 c2 a) (dt2 c1 b) (dt2 c2 b)
    hm hn h1 h2 h3 h4 (plucker c1 c2 a b)
  unfold Hv
  linear_combination this

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeSign
