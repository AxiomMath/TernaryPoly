module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLocal

@[expose] public section


/-!
# The twisted Heisenberg coordinates and the value of the plane cup class on the Heisenberg cycle

Formalized by Claude Sonnet 5.5.

For Heisenberg coordinates `(a, b, c)` the triple `(a', b', c') = (-b, -a, a b - c)` is again a system of Heisenberg coordinates (`heisTwist`); these are the coordinates of the image
of a unipotent matrix under the involution exchanging lines and planes.  `heis_cycle_cup_twist`: the cup product of the cusp coordinate `b' = -a` with `β` of the twisted datum has the value `-2 p² q²`
on the Heisenberg cycle.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.FlagH3

variable {B : Type} [Group B]

/-- The twisted Heisenberg coordinates `(-b, -a, a b - c)`. -/
def heisTwist (H : HeisCoords B) : HeisCoords B where
  a g := - H.b g
  b g := - H.a g
  c g := H.a g * H.b g - H.c g
  a_mul g h := by rw [H.b_mul]; ring
  b_mul g h := by rw [H.a_mul]; ring
  c_mul g h := by rw [H.a_mul, H.b_mul, H.c_mul]; ring
  inj g h h1 h2 h3 := by
    have e1 : H.b g = H.b h := by linarith
    have e2 : H.a g = H.a h := by linarith
    have e3 : H.c g = H.c h := by rw [e1, e2] at h3; linarith
    exact H.inj g h e2 e1 e3

theorem heis_cycle_cup_twist (H : HeisCoords B) (X Y : B) (p q : ℤ) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0)
    (hYa : H.a Y = 0) (hYb : H.b Y = q) (hYc : H.c Y = 0) :
    chainEval (heisCycle X Y) (fun g : Fin 3 → B => ((heisTwist H).b (g 0) : ℚ) * (heisLineData (heisTwist H)).beta (g 1) (g 2)) =
      -2 * (p : ℚ) ^ 2 * (q : ℚ) ^ 2 := by
  simp only [heisCycle, chainEval_add, chainEval_sub, chainEval_single, heisLineData_beta, heisTwist, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, TernaryPeriodPolynomials.Argument.FlagH3.comm, H.a_mul, H.b_mul, H.c_mul, H.a_inv, H.b_inv,
    H.c_inv, hXa, hXb, hXc, hYa, hYb, hYc]
  push_cast
  ring_nf

end TernaryPeriodPolynomials.Argument.GammaNStokes
