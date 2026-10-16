module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Decomp
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Action

@[expose] public section


/-!
# Smoothness of the triangular square root and its inverse (Appendix C.3)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### Smoothness of `planeP`, `planePinv` and uniform bounds on compacta -/

theorem contDiffAt_sqrt_coord {p : Fin 5 → ℝ} {k : Fin 5} (hk : 0 < p k) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => Real.sqrt (q k)) p :=
  ((contDiff_apply ℝ ℝ k).contDiffAt).sqrt hk.ne'

theorem contDiffAt_coord (p : Fin 5 → ℝ) (k : Fin 5) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => q k) p := (contDiff_apply ℝ ℝ k).contDiffAt

theorem contDiffAt_planePinv_entry {p : Fin 5 → ℝ} (hp : p ∈ Omega) (i j : Fin 3) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => planePinv q i j) p := by
  obtain ⟨hy, ht⟩ := hp
  have sy := contDiffAt_sqrt_coord hy
  have st := contDiffAt_sqrt_coord ht
  have c := contDiffAt_coord p
  have hsy : Real.sqrt (p 3) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hst : Real.sqrt (p 4) ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  fin_cases i <;> fin_cases j <;> simp only [planePinv, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk]
  · exact st.div sy hsy
  · exact (((c 2).neg).mul st).div sy hsy
  · exact (st.mul (((c 2).mul (c 1)).sub (c 0))).div sy hsy
  · exact contDiffAt_const
  · exact sy.mul st
  · exact (sy.mul st |>.mul (c 1)).neg
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const.div (c 4) ht.ne'

theorem contDiffAt_matToFun_planePinv {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => matToFun (planePinv q)) p := by
  rw [contDiffAt_pi]
  intro i
  rw [contDiffAt_pi]
  intro j
  exact contDiffAt_planePinv_entry hp i j

/-- For fixed `g` of determinant one, `planeAct g` is smooth at every point of `Ω`. -/
theorem contDiffAt_planeAct {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) : ContDiffAt ℝ ⊤ (planeAct g) x := by
  have h := contDiffAt_planeAct_pair hg hx
  exact h.comp x (contDiffAt_const.prodMk contDiffAt_id)

theorem differentiableAt_planeAct {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {x : Fin 5 → ℝ} (hx : x ∈ Omega) : DifferentiableAt ℝ (planeAct g) x :=
  (contDiffAt_planeAct hg hx).differentiableAt (by simp)

end TernaryPeriodPolynomials.Argument.ConvergenceC4
