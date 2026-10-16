module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Geom
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Radical

@[expose] public section


/-!
# The line radical: the closed-direction integral of a coset term with `r₀ = 0` vanishes

(row `Q, I`: "the target root
is conjugated into the source binary root `E₁₂`, possibly with a minus sign, which does not affect its
average"; the binary root average is zero by cuspidality).

Let `γ ∈ SL₃(ℤ)` have bottom row `(0, r₁, r₂)` (the line `ℚe₁` lies in the plane `ker r`) and let
`d' ∈ ℤ²` with `d'₀ r₁ - d'₁ r₂ ≠ 0`. Then `M_s = γ qMat(s N d') γ⁻¹` has bottom row `(0, 0, 1)` (the third
coordinate of `γ e₁` is `r₀ = 0`), hence lies in `P(ℝ)`, and `γ qMat(v + s N d') = M_s γ qMat v`. Its Levi block
is `I + s N N₀'` with `N₀' = -(γ e₁)_{01} ⊗ (d'₁ (γ⁻¹)_{1,01} + d'₀ (γ⁻¹)_{2,01})` integral, nilpotent and
nonzero. Exactly as in `UnfoldGeom.closed_direction_zero`, `rankOne_normalForm`, the summand at `M_s G` is the
summand at `G` for the form `h|A_s`, and `integral_unipConj_zero` (cuspidality) gives
`closed_direction_zero_Q`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.FormClassK

/-- The unipotent `g qMat(s d) g⁻¹`. -/
def conjQ (g gi : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 2 → ℝ) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  g * qMat (s • d) * gi

theorem conjQ_mul (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hgi : gi * g = 1) (d v : Fin 2 → ℝ) (s : ℝ) :
    conjQ g gi d s * (g * qMat v) = g * qMat (v + s • d) := by
  unfold conjQ
  calc g * qMat (s • d) * gi * (g * qMat v) = g * qMat (s • d) * (gi * g) * qMat v := by
        simp only [Matrix.mul_assoc]
    _ = g * (qMat (s • d) * qMat v) := by rw [hgi, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [qMat_mul, add_comm]

theorem det_conjQ (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det = 1) (hgi : gi * g = 1)
    (d : Fin 2 → ℝ) (s : ℝ) : (conjQ g gi d s).det = 1 := by
  have hgi' : gi.det = 1 := by
    have := congrArg Matrix.det hgi
    rw [Matrix.det_mul, hg, Matrix.det_one] at this
    simpa using this
  unfold conjQ
  rw [Matrix.det_mul, Matrix.det_mul, hg, hgi', det_qMat]; norm_num

/-- The bottom row of `g qMat(s d) g⁻¹` is `(0, 0, 1)` when `g₂₀ = 0`. -/
theorem conjQ_bottom (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hg : g * gi = 1) (h0 : g 2 0 = 0)
    (d : Fin 2 → ℝ) (s : ℝ) :
    conjQ g gi d s 2 0 = 0 ∧ conjQ g gi d s 2 1 = 0 ∧ conjQ g gi d s 2 2 = 1 := by
  have e : ∀ j, (g * gi) 2 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j := fun j => by rw [hg]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e0 e1 e2
  simp [h0] at e0 e1 e2
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [conjQ, qMat, Matrix.mul_apply, Fin.sum_univ_three, h0]
    first
    | linear_combination e0
    | linear_combination e1
    | linear_combination e2

theorem topBlock_conjQ (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hg : g * gi = 1) (d : Fin 2 → ℝ) (s : ℝ) :
    topBlock (conjQ g gi d s) = 1 + s • Matrix.vecMulVec (fun i : Fin 2 => -g i.castSucc 0)
      (fun j : Fin 2 => d 1 * gi 1 j.castSucc + d 0 * gi 2 j.castSucc) := by
  have e : ∀ i j, (g * gi) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by rw [hg]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e00 e01 e10 e11
  simp at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topBlock, conjQ, qMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMulVec] <;>
    first
    | linear_combination e00
    | linear_combination e01
    | linear_combination e10
    | linear_combination e11

/-- Integer facts about the data of `γ` (with `γ₂₀ = 0`) and the direction `d'`. -/
theorem geom_integer_facts_Q (γ : SL(3, ℤ)) (h0 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0)
    (d' : Fin 2 → ℤ)
    (hd : d' 0 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 - d' 1 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ≠ 0) :
    let a : Fin 2 → ℤ := fun i => -(γ : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 0
    let b : Fin 2 → ℤ := fun j => d' 1 * ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 j.castSucc +
      d' 0 * ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc
    a ≠ 0 ∧ b ≠ 0 ∧ a 0 * b 0 + a 1 * b 1 = 0 := by
  intro a b
  set M : Matrix (Fin 3) (Fin 3) ℤ := (γ : Matrix (Fin 3) (Fin 3) ℤ) with hM
  set Mi : Matrix (Fin 3) (Fin 3) ℤ := ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) with hMi
  have h2 : Mi * M = 1 := by
    rw [hM, hMi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have h3 : M * Mi = 1 := by
    rw [hM, hMi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have hdetM : M.det = 1 := γ.2
  have hdetMi : Mi.det = 1 := (γ⁻¹).2
  have f10 : Mi 1 0 * M 0 0 + Mi 1 1 * M 1 0 = 0 := by
    have := congrFun (congrFun h2 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0] at this
    linear_combination this
  have f20 : Mi 2 0 * M 0 0 + Mi 2 1 * M 1 0 = 0 := by
    have := congrFun (congrFun h2 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0] at this
    linear_combination this
  have g20 : M 2 1 * Mi 1 0 + M 2 2 * Mi 2 0 = 0 := by
    have := congrFun (congrFun h3 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0] at this
    linear_combination this
  have g21 : M 2 1 * Mi 1 1 + M 2 2 * Mi 2 1 = 0 := by
    have := congrFun (congrFun h3 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0] at this
    linear_combination this
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have a0 : M 0 0 = 0 := by have := congrFun hz 0; simpa [a] using this
    have a1 : M 1 0 = 0 := by have := congrFun hz 1; simpa [a] using this
    rw [Matrix.det_fin_three, a0, a1, h0] at hdetM
    simp at hdetM
  · intro hz
    have b0 : d' 1 * Mi 1 0 + d' 0 * Mi 2 0 = 0 := congrFun hz 0
    have b1 : d' 1 * Mi 1 1 + d' 0 * Mi 2 1 = 0 := congrFun hz 1
    have hΔ : d' 0 * M 2 1 - d' 1 * M 2 2 ≠ 0 := hd
    have z10 : Mi 1 0 = 0 := by
      apply (mul_eq_zero.mp (show (d' 0 * M 2 1 - d' 1 * M 2 2) * Mi 1 0 = 0 by
        linear_combination (d' 0) * g20 - (M 2 2) * b0)).resolve_left hΔ
    have z20 : Mi 2 0 = 0 := by
      apply (mul_eq_zero.mp (show (d' 0 * M 2 1 - d' 1 * M 2 2) * Mi 2 0 = 0 by
        linear_combination (M 2 1) * b0 - (d' 1) * g20)).resolve_left hΔ
    have z11 : Mi 1 1 = 0 := by
      apply (mul_eq_zero.mp (show (d' 0 * M 2 1 - d' 1 * M 2 2) * Mi 1 1 = 0 by
        linear_combination (d' 0) * g21 - (M 2 2) * b1)).resolve_left hΔ
    have z21 : Mi 2 1 = 0 := by
      apply (mul_eq_zero.mp (show (d' 0 * M 2 1 - d' 1 * M 2 2) * Mi 2 1 = 0 by
        linear_combination (M 2 1) * b1 - (d' 1) * g21)).resolve_left hΔ
    rw [Matrix.det_fin_three, z10, z20, z11, z21] at hdetMi
    simp at hdetMi
  · show -(M 0 0) * (d' 1 * Mi 1 0 + d' 0 * Mi 2 0) + -(M 1 0) * (d' 1 * Mi 1 1 + d' 0 * Mi 2 1) = 0
    linear_combination (-(d' 1)) * f10 - (d' 0) * f20

/-- **The closed-direction integral vanishes for a coset with `r₀ = 0`** (row `Q, I`): for `γ` with
bottom row `(0, r₁, r₂)` and `d' ∈ ℤ²` with `d'₀ r₁ - d'₁ r₂ ≠ 0`, the integral over one period of the
direction `N d'` of every coefficient of `S_h(γ qMat(v + s N d'))(x)` is zero (cuspidality). -/
theorem closed_direction_zero_Q (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (γ : SL(3, ℤ))
    (h0 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0) (d' : Fin 2 → ℤ)
    (hd : d' 0 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 - d' 1 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ≠ 0)
    (v : Fin 2 → ℝ) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (c : Fin 5 → Fin 5 → ℂ) (m : Fin 3 →₀ ℕ) :
    ∫ s in (0 : ℝ)..1, ∑ i : Fin 5, ∑ j : Fin 5,
      c i j * (summandPoly n (hfun f) (realMat γ * qMat (v + s • ((N : ℝ) • intVec d')))
        x i j).coeff m = 0 := by
  obtain ⟨ha', hb', hab⟩ := geom_integer_facts_Q γ h0 d' hd
  set a' : Fin 2 → ℤ := fun i => -(γ : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 0 with ha'def
  set b' : Fin 2 → ℤ := fun j => d' 1 * ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 j.castSucc +
      d' 0 * ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc with hb'def
  obtain ⟨B, μ', hμ'0, hmat⟩ := rankOne_normalForm a' b' ha' hb' hab
  set g := realMat γ with hgdef
  set gi := realMat γ⁻¹ with higdef
  have hg1 : g * gi = 1 := by rw [hgdef, higdef, ← realMat_mul, mul_inv_cancel, realMat_one]
  have hg2 : gi * g = 1 := by rw [hgdef, higdef, ← realMat_mul, inv_mul_cancel, realMat_one]
  have hgdet : g.det = 1 := det_realMat γ
  have hg20 : g 2 0 = 0 := by
    rw [hgdef, realMat_apply, h0]; simp
  set D : Fin 2 → ℝ := (N : ℝ) • intVec d' with hD
  set G := g * qMat v with hG
  have hGdet : G.det = 1 := by rw [hG, Matrix.det_mul, hgdet, det_qMat]; norm_num
  have hμ : (N : ℤ) ∣ (N : ℤ) * μ' := dvd_mul_right _ _
  have hμ0 : (N : ℤ) * μ' ≠ 0 := mul_ne_zero (by exact_mod_cast NeZero.ne N) hμ'0
  have hxτ := seedTau_im_pos (planeAct_mem hGdet hx)
  have key : ∀ (s : ℝ) (i j : Fin 5), (summandPoly n (hfun f) (g * qMat (v + s • D)) x i j).coeff m =
      slashTwisted (n + 3) (unipConj B (((N : ℤ) * μ' : ℤ) * s)) (hfun f)
        (seedTau (planeAct G x)) * Kfun n G x i j m := by
    intro s i j
    have hbot := conjQ_bottom g gi hg1 hg20 D s
    have hpar := eq_parabolicMatrix_of_bottom (conjQ g gi D s) hbot.1 hbot.2.1 hbot.2.2
    have hdetA : (topBlock (conjQ g gi D s)).det = 1 := by
      have h1 := det_conjQ g gi hgdet hg2 D s
      rw [hpar, SeedC3.det_parabolicMatrix] at h1
      exact h1
    have hblock : topBlock (conjQ g gi D s) = unipConj B (((N : ℤ) * μ' : ℤ) * s) := by
      rw [topBlock_conjQ g gi hg1 D s, unipConj_eq]
      congr 1
      have hcast : Matrix.vecMulVec (fun i : Fin 2 => -g i.castSucc 0)
          (fun j : Fin 2 => D 1 * gi 1 j.castSucc + D 0 * gi 2 j.castSucc) =
          (((N : ℤ) * μ' : ℤ) : ℝ) • (((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
            (Int.castRingHom ℝ) * !![0, 1; 0, 0] *
            (B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) := by
        ext p q
        have hent := congrFun (congrFun hmat p) q
        have hent' := congrArg (Int.cast : ℤ → ℝ) hent
        fin_cases p <;> fin_cases q <;>
        · simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
            Fin.sum_univ_two, Matrix.map_apply] at hent hent' ⊢
          simp [a', b', hgdef, higdef, realMat_apply, hD, intVec, Matrix.of_apply] at hent' ⊢
          linear_combination (N : ℝ) * hent'
      rw [hcast, smul_smul, mul_comm s]
    rw [← conjQ_mul g gi hg2 D v s, hpar,
      summandPoly_parabolic_mul n (hfun f) (topBlock (conjQ g gi D s)) hdetA _ hGdet hx i j,
      coeff_summandPoly_eq n _ hGdet, hblock]
  simp_rw [key]
  have hfac : ∀ s : ℝ, ∑ i : Fin 5, ∑ j : Fin 5, c i j *
      (slashTwisted (n + 3) (unipConj B (((N : ℤ) * μ' : ℤ) * s)) (hfun f)
        (seedTau (planeAct G x)) * Kfun n G x i j m) =
      slashTwisted (n + 3) (unipConj B (((N : ℤ) * μ' : ℤ) * s)) (hfun f)
        (seedTau (planeAct G x)) * ∑ i : Fin 5, ∑ j : Fin 5, c i j * Kfun n G x i j m := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hfac]
  rw [intervalIntegral.integral_mul_const,
    integral_unipConj_zero N n f B _ hμ0 hμ _ hxτ, zero_mul]


end TernaryPeriodPolynomials.Argument.EisensteinClass
