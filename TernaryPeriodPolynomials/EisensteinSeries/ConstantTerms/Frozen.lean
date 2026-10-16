module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Convergence
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ParabolicEquivariance

@[expose] public section


/-!
# The summand with base point (Appendix C.3, `ar:eq:seed-transform`)

For `B = P(p'')` triangular, `B^* ω_h = ρ(B) ω_{h_A}` at every point (`seed_closed_equivariant` clauses
(ii), (iii)). With the decomposition `Φ_g = Φ_B ∘ Φ_k ∘ Φ_{P(q)⁻¹}` at a base point `q` this gives, for
every `x ∈ Ω`, `S_g(x) = C(s̃(x)) ℓ̃(x)^n` where `s̃` is the scalar pullback by `R = Φ_k Φ_{P(q)⁻¹}`
of `h_A β ∧ dτ` and `ℓ̃` has bounded coefficients: all decay is in `h_A`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### The pullback by a triangular matrix at every point (the paper's `ar:eq:seed-transform`) -/

theorem rho_diagMat (A : Matrix (Fin 2) (Fin 2) ℝ) (T : ℝ) (hA : A.det ≠ 0) (hT : T ≠ 0)
    (q : MvPolynomial (Fin 3) ℂ) : leviCoefficientAction A T q = SeedC3.rho (diagMat A T) q := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = A.det := (Matrix.det_fin_two A).symm
  have hinv : (diagMat A T)⁻¹ = diagMat !![A 1 1 / A.det, -A 0 1 / A.det; -A 1 0 / A.det,
      A 0 0 / A.det] T⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagMat, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> linarith
  unfold leviCoefficientAction SeedC3.rho
  rw [hinv, det_diagMat]
  congr 1
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [diagMat, Fin.sum_univ_three]

theorem rho_transMat (v w : ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    bind₁ (![X 0 - C (v : ℂ) * X 2, X 1 - C (w : ℂ) * X 2, X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℂ) q = SeedC3.rho (transMat v w) q := by
  have hinv : (transMat v w)⁻¹ = transMat (-v) (-w) := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transMat, Matrix.mul_apply, Fin.sum_univ_three]
  unfold SeedC3.rho
  rw [hinv, det_transMat]
  simp only [inv_one, Complex.ofReal_one, map_one, one_mul]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [transMat, Fin.sum_univ_three, sub_eq_add_neg]

theorem formPullback_planeP (n : ℕ) (h : ℂ → ℂ) {p : Fin 5 → ℝ} (hp : p ∈ Omega)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    formPullback (planeAct (planeP p)) (seedForm n h) y a b =
      SeedC3.rho (planeP p) (seedForm n (slashTwisted (n + 3) (planeA p) h) y a b) := by
  set A := planeA p with hA
  have hT : 0 < p 4 := hp.2
  have hdetA : A.det * p 4 = 1 := det_planeA hp
  have hApos : 0 < A.det := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hd : (diagMat A (p 4)).det = 1 := by rw [det_diagMat]; exact hdetA
  have hΦ : ∀ x ∈ Omega,
      planeAct (planeP p) x = leviMap A (p 4) x + ![p 0, p 1, 0, 0, 0] := by
    intro x hx
    have hm : leviMap A (p 4) x ∈ Omega := by
      rw [← planeAct_diag A (p 4) hApos hT hdetA hx]; exact planeAct_mem hd hx
    rw [planeP_eq_mul, planeAct_mul hd hx, planeAct_diag A (p 4) hApos hT hdetA hx,
      planeAct_transMat (p 0) (p 1) hm]
  have hev : planeAct (planeP p) =ᶠ[nhds y]
      fun x => leviMap A (p 4) x + ![p 0, p 1, 0, 0, 0] :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hy) hΦ
  rw [formPullback_congr _ hev, SeedC3.formPullback_translate,
    (TernaryPeriodPolynomials.seed_closed_equivariant n h).2.2.1 A (p 4) hApos hT y hy.1 a b,
    rho_diagMat A (p 4) hApos.ne' hT.ne', rho_transMat, rho_mul, ← planeP_eq_mul]

/-! ### The summand as a linear functional of `h_A`, with base point -/

theorem differentiableAt_decompR_of_mem {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    DifferentiableAt ℝ (decompR g q) x := by
  have h1 : DifferentiableAt ℝ (planeAct (planePinv q)) x :=
    differentiableAt_planeAct (det_planePinv hq) hx
  have h2 : DifferentiableAt ℝ (planeAct (kFactor g q)) (planeAct (planePinv q) x) :=
    differentiableAt_planeAct (det_kFactor hg hq) (planeAct_mem (det_planePinv hq) hx)
  exact h2.comp x h1

theorem decompR_mem {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) {x : Fin 5 → ℝ} (hx : x ∈ Omega) : decompR g q x ∈ Omega :=
  planeAct_mem (det_kFactor hg hq) (planeAct_mem (det_planePinv hq) hx)

theorem g_mul_eq {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) :
    g * (planeP q * (kFactor g q).transpose) = planeP (planeAct g q) := by
  have hq'' := planeAct_mem hg hq
  have hk := kFactor_orth hg hq
  have hk' : (kFactor g q).transpose * kFactor g q = 1 := mul_eq_one_comm.1 hk
  have e : g * planeP q = planeP (planeAct g q) * kFactor g q := by
    unfold kFactor
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, planeP_mul_planePinv hq'', Matrix.one_mul]
  calc g * (planeP q * (kFactor g q).transpose) = (g * planeP q) * (kFactor g q).transpose := by
        rw [Matrix.mul_assoc]
    _ = planeP (planeAct g q) * (kFactor g q * (kFactor g q).transpose) := by
        rw [e, Matrix.mul_assoc]
    _ = planeP (planeAct g q) := by rw [hk, Matrix.mul_one]

theorem inv_g_mul {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) :
    g⁻¹ * planeP (planeAct g q) = planeP q * (kFactor g q).transpose := by
  have hu : IsUnit g.det := by rw [hg]; exact isUnit_one
  rw [← g_mul_eq hg hq, Matrix.nonsing_inv_mul_cancel_left g _ hu]

theorem rho_C_mul_pow_linear (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.det = 1) (s : ℂ)
    (c : Fin 3 → ℂ) (n : ℕ) :
    SeedC3.rho G (C s * (∑ k : Fin 3, C (c k) * X k) ^ n) =
      C s * (∑ l : Fin 3, C (∑ k : Fin 3, c k * ((G⁻¹ k l : ℝ) : ℂ)) * X l) ^ n := by
  unfold SeedC3.rho
  rw [map_mul, map_pow, bind₁_C_right, hG]
  simp only [inv_one, Complex.ofReal_one, map_one, one_mul]
  rw [bind_linear c G⁻¹]

theorem det_stab_factor {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) : (planeP q * (kFactor g q).transpose).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_transpose, det_planeP hq, det_kFactor hg hq]; norm_num

theorem stab_factor_inv {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) :
    (planeP q * (kFactor g q).transpose)⁻¹ = kFactor g q * planePinv q := by
  have hk := kFactor_orth hg hq
  have hk' : (kFactor g q).transpose * kFactor g q = 1 := mul_eq_one_comm.1 hk
  refine Matrix.inv_eq_right_inv ?_
  calc planeP q * (kFactor g q).transpose * (kFactor g q * planePinv q)
      = planeP q * ((kFactor g q).transpose * kFactor g q) * planePinv q := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hk', Matrix.mul_one, planeP_mul_planePinv hq]

/-- **The base formula.** For `x ∈ Ω`, with the data `k, B` attached to the base point `q`,
`S_g(x) = C(s̃(x)) ℓ̃(x)^n` where `s̃` is the scalar pullback by `R = Φ_k ∘ Φ_{P(q)⁻¹}` of
`h_A β ∧ dτ` and the coefficients of `ℓ̃` are bounded (they involve only `R x`, `k` and
`P(q)⁻¹`), while all the decay `b^{-k}` sits in `h_A`. -/
theorem summandPoly_frozen (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) :
    summandPoly n h g x i j =
      C (scalarPullback (decompR g q)
          (seedForm0 (slashTwisted (n + 3) (planeA (planeAct g q)) h)) x i j) *
        (∑ l : Fin 3, C (∑ k : Fin 3, seedRow (decompR g q x) k *
          (((kFactor g q * planePinv q) k l : ℝ) : ℂ)) * X l) ^ n := by
  have hq'' := planeAct_mem hg hq
  have hB := det_planeP hq''
  have hev : planeAct g =ᶠ[nhds x] planeAct (planeP (planeAct g q)) ∘ decompR g q :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hx) fun z hz => planeAct_decomp hg hq hz
  unfold summandPoly
  rw [formPullback_congr _ hev, formPullback_comp _ _ _ x
      (differentiableAt_decompR_of_mem hg hq hx)
      (differentiableAt_planeAct hB (decompR_mem hg hq hx)) i j]
  rw [formPullback_congr_form (Φ := decompR g q)
      (ν' := fun y a b => SeedC3.rho (planeP (planeAct g q))
        (seedForm n (slashTwisted (n + 3) (planeA (planeAct g q)) h) y a b)) x
      (fun a b => formPullback_planeP n h hq'' (decompR_mem hg hq hx) a b) i j,
    formPullback_rho, rho_mul, inv_g_mul hg hq, formPullback_seedForm, seedLinear_eq_sum,
    rho_C_mul_pow_linear _ (det_stab_factor hg hq), stab_factor_inv hg hq]

end TernaryPeriodPolynomials.Argument.ConvergenceC4
