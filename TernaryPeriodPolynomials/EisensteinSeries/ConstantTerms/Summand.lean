module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Decomp
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.BaseScalar
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Scalar
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.LinearForm
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.PolyNorm
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Smooth
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RhoAction

@[expose] public section


/-!
# The summand of the series `ar:eq:Eseries` (Appendix C.3, `ar:sec:series`)

`summandPoly n h g q i j = ρ(g)⁻¹ (g^* ω_h)_q(eᵢ, eⱼ)` for `g ∈ SL₃(ℝ)`. It factors as
`C s * (ℓ)^n` with the scalar `s` (pullback of `h β ∧ dτ`) and the transformed linear form `ℓ`,
and `s` is controlled through the decomposition `Φ_g = Φ_{P(gq)} ∘ Φ_k ∘ Φ_{P(q)⁻¹}`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The scalar part of the summand: decomposition and bound -/

/-- The composite `Φ_k ∘ Φ_{P(q)⁻¹}` of the decomposition. -/
def decompR (g : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin 5 → ℝ) : (Fin 5 → ℝ) → (Fin 5 → ℝ) :=
  planeAct (kFactor g q) ∘ planeAct (planePinv q)

theorem decompR_apply_self {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) : decompR g q q = basePt := by
  simp [decompR, Function.comp, planeAct_planePinv_self hq,
    planeAct_basePt_of_orthogonal (kFactor_orth hg hq)]

theorem differentiableAt_decompR {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) : DifferentiableAt ℝ (decompR g q) q := by
  have h1 : DifferentiableAt ℝ (planeAct (planePinv q)) q :=
    differentiableAt_planeAct (det_planePinv hq) hq
  have h2 : DifferentiableAt ℝ (planeAct (kFactor g q)) (planeAct (planePinv q) q) := by
    rw [planeAct_planePinv_self hq]
    exact differentiableAt_planeAct (det_kFactor hg hq) basePt_mem
  exact h2.comp q h1

theorem scalar_decomp (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    scalarPullback (planeAct g) (seedForm0 h) q i j =
      ∑ a : Fin 5, ∑ b : Fin 5,
        ((fderiv ℝ (decompR g q) q (Pi.single i 1) a *
          fderiv ℝ (decompR g q) q (Pi.single j 1) b : ℝ) : ℂ) *
        seedForm0 (slashTwisted 3 (planeA (planeAct g q)) h) basePt a b := by
  have hq'' := planeAct_mem hg hq
  have hev : planeAct g =ᶠ[nhds q] (planeAct (planeP (planeAct g q))) ∘ decompR g q := by
    refine Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun x hx => ?_
    exact planeAct_decomp hg hq hx
  have hRq := decompR_apply_self hg hq
  have h₂ : DifferentiableAt ℝ (planeAct (planeP (planeAct g q))) (decompR g q q) := by
    rw [hRq]
    exact differentiableAt_planeAct (det_planeP hq'') basePt_mem
  rw [scalarPullback_congr _ hev, scalarPullback_comp _ _ _ _ (differentiableAt_decompR hg hq) h₂]
  show ∑ a : Fin 5, ∑ b : Fin 5, _ = _
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hRq, scalar_planeP_basePt h hq'' a b]

theorem norm_seedBeta_le (c : Fin 5) : ‖seedBeta basePt c‖ ≤ 1 := by
  fin_cases c <;> simp [seedBeta, seedTau, basePt]

theorem norm_seedDTau_le (c : Fin 5) : ‖seedDTau c‖ ≤ 1 := by
  fin_cases c <;> simp [seedDTau]

theorem norm_seedForm0_basePt_le (h : ℂ → ℂ) (a b : Fin 5) :
    ‖seedForm0 h basePt a b‖ ≤ 2 * ‖h (seedTau basePt)‖ := by
  unfold seedForm0
  rw [norm_mul]
  have : ‖seedBeta basePt a * seedDTau b - seedBeta basePt b * seedDTau a‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := norm_seedBeta_le a
    have h2 := norm_seedDTau_le b
    have h3 := norm_seedBeta_le b
    have h4 := norm_seedDTau_le a
    nlinarith [norm_nonneg (seedBeta basePt a), norm_nonneg (seedDTau b),
      norm_nonneg (seedBeta basePt b), norm_nonneg (seedDTau a)]
  nlinarith [norm_nonneg (h (seedTau basePt))]

/-- Bound of the scalar part of the summand. -/
theorem norm_scalar_summand_le (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) (N : ℝ)
    (hN : ∀ c, |fderiv ℝ (decompR g q) q (Pi.single i 1) c| ≤ N ∧
      |fderiv ℝ (decompR g q) q (Pi.single j 1) c| ≤ N) :
    ‖scalarPullback (planeAct g) (seedForm0 h) q i j‖ ≤
      25 * (N * N * (2 * ((Real.sqrt (planeAct g q 3) / Real.sqrt (planeAct g q 4)) ^ 3 *
        ‖h (seedTau (planeAct g q))‖))) := by
  have hq'' := planeAct_mem hg hq
  rw [scalar_decomp h hg hq]
  have := norm_scalarPullback_le (decompR g q)
    (fun _ a b => seedForm0 (slashTwisted 3 (planeA (planeAct g q)) h) basePt a b) q i j N
    (2 * ((Real.sqrt (planeAct g q 3) / Real.sqrt (planeAct g q 4)) ^ 3 *
        ‖h (seedTau (planeAct g q))‖)) hN (fun a b => by
      refine (norm_seedForm0_basePt_le _ a b).trans ?_
      rw [norm_slash_planeA h hq''])
  exact this

/-! ### The summand polynomial and its coefficient bound -/

/-- The summand `ρ(g)⁻¹ g^* ω_h` of the series `ar:eq:Eseries` at the point `q`. -/
def summandPoly (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin 5 → ℝ) (i j : Fin 5) :
    MvPolynomial (Fin 3) ℂ :=
  SeedC3.rho g⁻¹ (formPullback (planeAct g) (seedForm n h) q i j)

theorem bind_linear (c : Fin 3 → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C ((g i j : ℝ) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ))
        (∑ i : Fin 3, C (c i) * X i) =
      ∑ j : Fin 3, C (∑ i : Fin 3, c i * (g i j : ℂ)) * X j := by
  simp only [Fin.sum_univ_three, map_add, map_mul, bind₁_X_right, bind₁_C_right]
  ring

theorem summandPoly_eq (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    (q : Fin 5 → ℝ) (i j : Fin 5) :
    summandPoly n h g q i j =
      C (scalarPullback (planeAct g) (seedForm0 h) q i j) *
        (∑ l : Fin 3, C (∑ k : Fin 3, seedRow (planeAct g q) k * (g k l : ℂ)) * X l) ^ n := by
  have hu : IsUnit g.det := by rw [hg]; exact isUnit_one
  have hdet : ((g⁻¹).det)⁻¹ = (1 : ℝ) := by
    rw [Matrix.det_nonsing_inv, hg]; simp
  have hinv : (g⁻¹)⁻¹ = g := Matrix.nonsing_inv_nonsing_inv g hu
  unfold summandPoly SeedC3.rho
  rw [formPullback_seedForm, seedLinear_eq_sum, hdet, hinv]
  simp only [Complex.ofReal_one, map_one, one_mul, map_mul, map_pow, bind₁_C_right]
  rw [bind_linear]

/-- Coefficient bound of the summand in terms of the three scalar quantities. -/
theorem coeff_summand_le (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    (q : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ‖(summandPoly n h g q i j).coeff m‖ ≤
      ‖scalarPullback (planeAct g) (seedForm0 h) q i j‖ *
        (∑ l : Fin 3, ‖∑ k : Fin 3, seedRow (planeAct g q) k * (g k l : ℂ)‖) ^ n := by
  rw [summandPoly_eq n h hg]
  refine (norm_coeff_le_l1 _ m).trans ?_
  rw [l1_C_mul]
  refine mul_le_mul_of_nonneg_left ((l1_pow_le _ n).trans ?_) (norm_nonneg _)
  exact pow_le_pow_left₀ (l1_nonneg _) (l1_linear_le _) n

end TernaryPeriodPolynomials.Argument.ConvergenceC4
