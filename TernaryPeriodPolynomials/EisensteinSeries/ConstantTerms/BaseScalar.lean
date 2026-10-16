module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Levi
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Scalar
public import TernaryPeriodPolynomials.BoundaryComparison.StokesComparison

@[expose] public section


/-!
# The scalar pullback by a triangular matrix at the base point (Appendix C.3)

The scalar part `h(τ) β ∧ dτ` of the seed pulled back by `planeAct (planeP p)` at the base point is
the weight-three slash transform of `h` (`seed_closed_equivariant`, clauses (ii) and (iii) at `n = 0`),
whose norm is `(√y/√t)³ ‖h(τ)‖`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The scalar part of the pullback by a triangular matrix at the base point -/

theorem seedForm0_shift (h : ℂ → ℂ) (p : Fin 5 → ℝ) (v w : ℝ) (a b : Fin 5) :
    seedForm0 h (p + ![v, w, 0, 0, 0]) a b = seedForm0 h p a b := by
  simp [seedForm0, seedTau, seedBeta]

theorem scalarPullback_shift (h : ℂ → ℂ) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (v w : ℝ)
    (p : Fin 5 → ℝ) (i j : Fin 5) :
    scalarPullback (fun x => Φ x + ![v, w, 0, 0, 0]) (seedForm0 h) p i j =
      scalarPullback Φ (seedForm0 h) p i j := by
  unfold scalarPullback
  rw [fderiv_add_const]
  simp only [seedForm0_shift]

theorem scalarPullback_congr (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → ℂ)
    {Φ₁ Φ₂ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {p : Fin 5 → ℝ} (h : Φ₁ =ᶠ[nhds p] Φ₂) (i j : Fin 5) :
    scalarPullback Φ₁ ω p i j = scalarPullback Φ₂ ω p i j := by
  unfold scalarPullback
  rw [h.fderiv_eq, h.eq_of_nhds]

theorem isOpen_Omega : IsOpen Omega := by
  have h1 : IsOpen {p : Fin 5 → ℝ | 0 < p 3} :=
    isOpen_lt continuous_const (continuous_apply 3)
  have h2 : IsOpen {p : Fin 5 → ℝ | 0 < p 4} :=
    isOpen_lt continuous_const (continuous_apply 4)
  exact h1.inter h2

/-- The scalar pullback of `h(τ) β ∧ dτ` by the triangular matrix `P(p)` at the base point is the
weight-three slash transform of `h`, by the `seed_closed_equivariant`. -/
theorem scalar_planeP_basePt (h : ℂ → ℂ) {p : Fin 5 → ℝ} (hp : p ∈ Omega) (a b : Fin 5) :
    scalarPullback (planeAct (planeP p)) (seedForm0 h) basePt a b =
      seedForm0 (slashTwisted 3 (planeA p) h) basePt a b := by
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
  have hev : planeAct (planeP p) =ᶠ[nhds basePt]
      fun x => leviMap A (p 4) x + ![p 0, p 1, 0, 0, 0] :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds basePt_mem) hΦ
  rw [scalarPullback_congr _ hev, scalarPullback_shift]
  have key := (TernaryPeriodPolynomials.seed_closed_equivariant 0 h).2.2.1 A (p 4) hApos hT basePt
    (by simp [basePt]) a b
  have e1 : formPullback (leviMap A (p 4)) (seedForm 0 h) basePt a b =
      C (scalarPullback (leviMap A (p 4)) (seedForm0 h) basePt a b) := by
    rw [formPullback_seedForm, pow_zero, mul_one]
  have e2 : leviCoefficientAction A (p 4) (seedForm 0 (slashTwisted (0 + 3) A h) basePt a b) =
      C (seedForm0 (slashTwisted 3 A h) basePt a b) := by
    rw [seedForm_eq_C_mul, pow_zero, mul_one]
    unfold leviCoefficientAction
    rw [bind₁_C_right, ← C_mul, hdetA]
    simp
  exact MvPolynomial.C_injective _ _ (e1.symm.trans (key.trans e2))

/-- The weight-three slash transform of `planeA p` at `i` has norm `(√y/√t)³ ‖h(τ)‖`. -/
theorem norm_slash_planeA (h : ℂ → ℂ) {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    ‖slashTwisted 3 (planeA p) h (seedTau basePt)‖ =
      (Real.sqrt (p 3) / Real.sqrt (p 4)) ^ 3 * ‖h (seedTau p)‖ := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have hsa : Real.sqrt (p 3) = a := by rw [e3]; exact Real.sqrt_sq ha.le
  have hsb : Real.sqrt (p 4) = b := by rw [e4]; exact Real.sqrt_sq hb.le
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hy : (p 3 : ℂ) = (a : ℂ) ^ 2 := by exact_mod_cast e3
  have hτ : (((planeA p 0 0 : ℝ) : ℂ) * seedTau basePt + (planeA p 0 1 : ℝ)) /
      (((planeA p 1 0 : ℝ) : ℂ) * seedTau basePt + (planeA p 1 1 : ℝ)) = seedTau p := by
    simp [planeA, seedTau, basePt, hsa, hsb]
    field_simp
    rw [hy]; ring
  unfold slashTwisted
  rw [hτ]
  simp [planeA, Matrix.det_fin_two, seedTau, basePt, hsa, hsb, norm_pow,
    Complex.norm_real, abs_of_pos ha, abs_of_pos hb]
  left
  field_simp


end TernaryPeriodPolynomials.Argument.ConvergenceC4
