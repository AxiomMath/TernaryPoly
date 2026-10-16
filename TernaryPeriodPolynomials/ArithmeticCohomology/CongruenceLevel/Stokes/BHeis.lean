module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLineData

@[expose] public section


/-!
# The standard line datum of Heisenberg coordinates and its value on the Heisenberg cycle

Formalized by Claude Sonnet 5.5.

For a group `B` with Heisenberg coordinates `(a, b, c)` (entries `01, 12, 02` of a unipotent upper triangular matrix) the pair `A = [[1, b], [0, 1]]`, `v = (a, c)` is a line datum
(`heisLineData`).  The cup product of the additive function `b` with its `β` has the value `-2 p² q²` on the Heisenberg cycle `heisCycle X Y` (`heis_cycle_cup`), the same value as the
Heisenberg `3`-cocycle `θ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.FlagH3

variable {B : Type} [Group B]

/-- The standard line datum of Heisenberg coordinates. -/
def heisLineData (H : HeisCoords B) : LineData B where
  A g := !![1, (H.b g : ℤ); 0, 1]
  v g := ![H.a g, H.c g]
  A_mul g h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, H.b_mul]; try ring
  det_one g := by simp [Matrix.det_fin_two]
  v_mul g h := by
    ext i; fin_cases i <;> simp [H.a_mul, H.c_mul]; try ring

theorem heisLineData_beta (H : HeisCoords B) (g h : B) :
    (heisLineData H).beta g h = (H.a g : ℚ) * H.c h - ((H.a g : ℚ) * H.b h + H.c g) * H.a h := by
  simp [LineData.beta, heisLineData, omega, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- **The value of `b ∪ β` on the Heisenberg cycle.** -/
theorem heis_cycle_cup (H : HeisCoords B) (X Y : B) (p q : ℤ) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0)
    (hYa : H.a Y = 0) (hYb : H.b Y = q) (hYc : H.c Y = 0) :
    chainEval (heisCycle X Y) (fun g : Fin 3 → B => (H.b (g 0) : ℚ) * (heisLineData H).beta (g 1) (g 2)) =
      -2 * (p : ℚ) ^ 2 * (q : ℚ) ^ 2 := by
  simp only [heisCycle, chainEval_add, chainEval_sub, chainEval_single, heisLineData_beta, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, TernaryPeriodPolynomials.Argument.FlagH3.comm, H.a_mul, H.b_mul, H.c_mul, H.a_inv, H.b_inv,
    H.c_inv, hXa, hXb, hXc, hYa, hYb, hYc]
  push_cast
  ring_nf

end TernaryPeriodPolynomials.Argument.GammaNStokes
