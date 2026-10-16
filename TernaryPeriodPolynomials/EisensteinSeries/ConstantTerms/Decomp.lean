module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Action

@[expose] public section


/-!
# The triangular-orthogonal decomposition of `g P(q)` (Appendix C.3, `ar:sec:series`)

For `g ∈ SL₃(ℝ)` and `q ∈ Ω` write `g P(q) = B k` with `B = P(g q)` triangular and `k` orthogonal;
then `Φ_g = Φ_B ∘ Φ_k ∘ Φ_{P(q)⁻¹}` and `Φ_{P(q)⁻¹} q` is the base point.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The inverse of `planeP` and the Iwasawa-type decomposition -/

/-- The explicit inverse of the triangular matrix `planeP p`. -/
def planePinv (p : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt (p 4) / Real.sqrt (p 3), -(p 2) * Real.sqrt (p 4) / Real.sqrt (p 3),
     Real.sqrt (p 4) * (p 2 * p 1 - p 0) / Real.sqrt (p 3);
     0, Real.sqrt (p 3) * Real.sqrt (p 4), -(Real.sqrt (p 3) * Real.sqrt (p 4) * p 1);
     0, 0, 1 / p 4]

theorem planeP_mul_planePinv {p : Fin 5 → ℝ} (hp : p ∈ Omega) : planeP p * planePinv p = 1 := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeP, planePinv, Matrix.mul_apply, Fin.sum_univ_three, e3, e4,
      Real.sqrt_sq ha.le, Real.sqrt_sq hb.le]
  all_goals field_simp
  all_goals ring

theorem planePinv_mul_planeP {p : Fin 5 → ℝ} (hp : p ∈ Omega) : planePinv p * planeP p = 1 :=
  mul_eq_one_comm.1 (planeP_mul_planePinv hp)

theorem det_planePinv {p : Fin 5 → ℝ} (hp : p ∈ Omega) : (planePinv p).det = 1 := by
  have := congrArg Matrix.det (planeP_mul_planePinv hp)
  rw [Matrix.det_mul, det_planeP hp, one_mul, Matrix.det_one] at this
  exact this

/-- The orthogonal factor of `g P(q) = B(g q) k`. -/
def kFactor (g : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  planePinv (planeAct g q) * g * planeP q

theorem kFactor_orth {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) : kFactor g q * (kFactor g q).transpose = 1 := by
  have hq'' := planeAct_mem hg hq
  have h1 : kFactor g q * (kFactor g q).transpose =
      planePinv (planeAct g q) * (g * (planeP q * (planeP q).transpose) * g.transpose) *
        (planePinv (planeAct g q)).transpose := by
    simp [kFactor, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h1, planeP_mul_transpose hq, ← planeGram_planeAct hg hq, ← planeP_mul_transpose hq'']
  have h2 : (planeP (planeAct g q)).transpose * (planePinv (planeAct g q)).transpose = 1 := by
    rw [← Matrix.transpose_mul, planePinv_mul_planeP hq'', Matrix.transpose_one]
  calc planePinv (planeAct g q) * (planeP (planeAct g q) * (planeP (planeAct g q)).transpose) *
        (planePinv (planeAct g q)).transpose
      = (planePinv (planeAct g q) * planeP (planeAct g q)) *
        ((planeP (planeAct g q)).transpose * (planePinv (planeAct g q)).transpose) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [planePinv_mul_planeP hq'', h2, Matrix.mul_one]

theorem det_kFactor {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) : (kFactor g q).det = 1 := by
  simp [kFactor, Matrix.det_mul, det_planePinv (planeAct_mem hg hq), hg, det_planeP hq]

theorem g_eq_decomp {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) :
    g = planeP (planeAct g q) * kFactor g q * planePinv q := by
  have hq'' := planeAct_mem hg hq
  unfold kFactor
  calc g = (planeP (planeAct g q) * planePinv (planeAct g q)) * g *
        (planeP q * planePinv q) := by
        rw [planeP_mul_planePinv hq'', planeP_mul_planePinv hq]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

theorem planeAct_decomp {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q x : Fin 5 → ℝ}
    (hq : q ∈ Omega) (hx : x ∈ Omega) :
    planeAct g x = planeAct (planeP (planeAct g q))
      (planeAct (kFactor g q) (planeAct (planePinv q) x)) := by
  have hq'' := planeAct_mem hg hq
  have hB : (planeP (planeAct g q)).det = 1 := det_planeP hq''
  have hk := det_kFactor hg hq
  have hI : (planePinv q).det = 1 := det_planePinv hq
  have hx' := planeAct_mem hI hx
  conv_lhs => rw [g_eq_decomp hg hq]
  rw [planeAct_mul hI hx, planeAct_mul hk hx']
  
/-- `Φ_{P(q)⁻¹}` sends `q` to the base point. -/
theorem planeAct_planePinv_self {q : Fin 5 → ℝ} (hq : q ∈ Omega) :
    planeAct (planePinv q) q = basePt := by
  have : planePinv q * planeGram q * (planePinv q).transpose = 1 := by
    rw [← planeP_mul_transpose hq]
    calc planePinv q * (planeP q * (planeP q).transpose) * (planePinv q).transpose
        = (planePinv q * planeP q) * ((planeP q).transpose * (planePinv q).transpose) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.transpose_mul, planePinv_mul_planeP hq]; simp
  simp [planeAct, this, planePoint_one]

end TernaryPeriodPolynomials.Argument.ConvergenceC4
