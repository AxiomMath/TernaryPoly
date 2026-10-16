module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Decomp
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Action
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section


/-!
# The transformed linear form of the summand (Appendix C.3, `ar:sec:series`)

The coefficient row `c = seedRow p` of `𝓑 = seedLinear p` satisfies the exact identity
`|c · P(p)|² = 2 y / t`. Since `Φ_g q` has Gram matrix `g P(q) P(q)ᵀ gᵀ`, the row `c · g` of the
transformed linear form is bounded by `3 Λ √(2 y'/t')` where `Λ` bounds `P(q)⁻¹`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The linear form: exact norm identity -/

/-- The coefficient row of `seedLinear p` in the basis `X, Y, Z`. -/
def seedRow (p : Fin 5 → ℝ) : Fin 3 → ℂ :=
  ![-1, seedTau p, (p 0 : ℂ) - seedTau p * (p 1 : ℂ)]

theorem seedLinear_eq_sum (p : Fin 5 → ℝ) :
    seedLinear p = ∑ j : Fin 3, C (seedRow p j) * X j := by
  simp [seedLinear, seedRow, Fin.sum_univ_three]
  ring

/-- `c · P(p)` for the coefficient row `c = seedRow p` is `(-√y/√t, i √y/√t, 0)`. -/
theorem seedRow_mul_planeP {p : Fin 5 → ℝ} (hp : p ∈ Omega) (k : Fin 3) :
    ∑ i : Fin 3, seedRow p i * (planeP p i k : ℂ) =
      ![((-(Real.sqrt (p 3) / Real.sqrt (p 4)) : ℝ) : ℂ),
        Complex.I * ((Real.sqrt (p 3) / Real.sqrt (p 4) : ℝ) : ℂ), 0] k := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsa : Real.sqrt (p 3) = a := by rw [e3]; exact Real.sqrt_sq ha.le
  have hsb : Real.sqrt (p 4) = b := by rw [e4]; exact Real.sqrt_sq hb.le
  have hy : (p 3 : ℂ) = (a : ℂ) ^ 2 := by exact_mod_cast e3
  have ht : (p 4 : ℂ) = (b : ℂ) ^ 2 := by exact_mod_cast e4
  fin_cases k <;>
    simp [seedRow, seedTau, planeP, Fin.sum_univ_three, hsa, hsb]
  all_goals (try field_simp)
  all_goals (try rw [hy])
  all_goals (try ring)

/-- The exact norm identity `|c · P(p)|² = 2 y / t`. -/
theorem sumsq_seedRow_planeP {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    ∑ k : Fin 3, ‖∑ i : Fin 3, seedRow p i * (planeP p i k : ℂ)‖ ^ 2 = 2 * p 3 / p 4 := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have hsa : Real.sqrt (p 3) = a := by rw [e3]; exact Real.sqrt_sq ha.le
  have hsb : Real.sqrt (p 4) = b := by rw [e4]; exact Real.sqrt_sq hb.le
  simp only [seedRow_mul_planeP hp, Fin.sum_univ_three, hsa, hsb]
  simp [Complex.norm_real, abs_of_pos ha, abs_of_pos hb, e3, e4]
  field_simp
  norm_num

/-- Quadratic form of a row vector against `M Mᵀ`. -/
theorem quad_rowvec (a : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ k : Fin 3, (∑ i : Fin 3, a i * M i k) ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, a i * a j * (M * M.transpose) i j := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- The squared norm of `c M` depends only on `M Mᵀ`, for a complex row vector `c`. -/
theorem sumsq_rowvec_eq (c : Fin 3 → ℂ) (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (h : M * M.transpose = N * N.transpose) :
    ∑ k : Fin 3, ‖∑ i : Fin 3, c i * (M i k : ℂ)‖ ^ 2 =
      ∑ k : Fin 3, ‖∑ i : Fin 3, c i * (N i k : ℂ)‖ ^ 2 := by
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3),
      ‖∑ i : Fin 3, c i * (M i k : ℂ)‖ ^ 2 =
        (∑ i : Fin 3, (c i).re * M i k) ^ 2 + (∑ i : Fin 3, (c i).im * M i k) ^ 2 := by
    intro M k
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Fin.sum_univ_three]
    ring
  simp only [key, Finset.sum_add_distrib, quad_rowvec, h]


/-! ### Bound of the transformed linear form -/

theorem rowForm_bound {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) (Λ : ℝ) (hΛ : ∀ l j, |planePinv q l j| ≤ Λ) (j : Fin 3) :
    ‖∑ i : Fin 3, seedRow (planeAct g q) i * (g i j : ℂ)‖ ≤
      3 * Λ * Real.sqrt (2 * planeAct g q 3 / planeAct g q 4) := by
  have hq'' := planeAct_mem hg hq
  set M := g * planeP q with hM
  have hMM : M * M.transpose = planeP (planeAct g q) * (planeP (planeAct g q)).transpose := by
    rw [planeP_mul_transpose hq'', planeGram_planeAct hg hq, ← planeP_mul_transpose hq]
    simp [hM, Matrix.transpose_mul, Matrix.mul_assoc]
  set c := seedRow (planeAct g q) with hc
  set v : Fin 3 → ℂ := fun l => ∑ i : Fin 3, c i * (M i l : ℂ) with hv
  have hsum : ∑ l : Fin 3, ‖v l‖ ^ 2 = 2 * planeAct g q 3 / planeAct g q 4 := by
    rw [← sumsq_seedRow_planeP hq'']
    exact sumsq_rowvec_eq c M (planeP (planeAct g q)) hMM
  have hvl : ∀ l, ‖v l‖ ≤ Real.sqrt (2 * planeAct g q 3 / planeAct g q 4) := by
    intro l
    rw [← hsum]
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun l => ‖v l‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ l)
  have hgM : g = M * planePinv q := by
    rw [hM, Matrix.mul_assoc, planeP_mul_planePinv hq, Matrix.mul_one]
  have hrow : ∑ i : Fin 3, c i * (g i j : ℂ) = ∑ l : Fin 3, v l * (planePinv q l j : ℂ) := by
    have : ∀ i, (g i j : ℂ) = ∑ l : Fin 3, (M i l : ℂ) * (planePinv q l j : ℂ) := by
      intro i
      conv_lhs => rw [hgM]
      simp [Matrix.mul_apply]
    simp only [this, hv, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hrow]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l : Fin 3, ‖v l * (planePinv q l j : ℂ)‖
      ≤ ∑ l : Fin 3, Real.sqrt (2 * planeAct g q 3 / planeAct g q 4) * Λ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hvl l) (hΛ l j) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = 3 * Λ * Real.sqrt (2 * planeAct g q 3 / planeAct g q 4) := by
        simp; ring


end TernaryPeriodPolynomials.Argument.ConvergenceC4
