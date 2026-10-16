module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Term
public import TernaryPeriodPolynomials.EisensteinSeries.Class.NilpNormal
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Cusp
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Periodic
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Instance
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Series

@[expose] public section


/-!
# The closed-direction integral of a non-identity coset term vanishes

(unfolding over the
nontrivial double coset: "the target root is conjugated into the source binary root").

Let `γ ∈ SL₃(ℤ)` have bottom row `(r', c₃)` with `r' ≠ 0` and let `d' ∈ ℤ²` be a nonzero vector with
`r'·d' = 0`. Then `M_s = γ n(s N d') γ⁻¹` has bottom row `(0, 0, 1)` (because `(γ d̃)₃ = r'·d' = 0`), hence
lies in `P(ℝ)`, and `γ n(v + s N d') = M_s γ n(v)`. Its Levi block is `I + s N₀` with
`N₀ = N (γ d̃')_{01} ⊗ (γ⁻¹)_{2,01}` integral, nilpotent and nonzero (`geom_integer_facts`; nonzero
because `r' ≠ 0`), i.e. `N₀ = μ B⁻¹ E₁₂ B` (`rankOne_normalForm`). By `summandPoly_parabolic_mul` the summand
at `M_s G` is the summand at `G` for the form `h|A_s`, and its coefficients are `h|A_s (τ*) × K` with `K`
independent of `s` (`coeff_summandPoly_eq`). `closed_direction_zero` then follows from
`integral_unipConj_zero` (cuspidality). This is the zero-Fourier-mode statement along the stabilizing
horocycle; it is NOT a statement that the average of a single coset vanishes (the orbit sum is needed,
`UnfoldOrbit.lean`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument

/-- The unipotent `g n(s d) g⁻¹`. -/
def conjU (g gi : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 2 → ℝ) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  g * nmat (s • d) * gi

theorem conjU_mul (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hgi : gi * g = 1) (d v : Fin 2 → ℝ) (s : ℝ) :
    conjU g gi d s * (g * nmat v) = g * nmat (v + s • d) := by
  unfold conjU
  calc g * nmat (s • d) * gi * (g * nmat v) = g * nmat (s • d) * (gi * g) * nmat v := by
        simp only [Matrix.mul_assoc]
    _ = g * (nmat (s • d) * nmat v) := by rw [hgi, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [nmat_mul, add_comm]

theorem det_conjU (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det = 1) (hgi : gi * g = 1)
    (d : Fin 2 → ℝ) (s : ℝ) : (conjU g gi d s).det = 1 := by
  have hgi' : gi.det = 1 := by
    have := congrArg Matrix.det hgi
    rw [Matrix.det_mul, hg, Matrix.det_one] at this
    simpa using this
  unfold conjU
  rw [Matrix.det_mul, Matrix.det_mul, hg, hgi', det_nmat]; norm_num

/-- The bottom row of `g n(s d) g⁻¹` is `(0, 0, 1)` when `d` is orthogonal to the first two bottom
entries of `g`. -/
theorem conjU_bottom (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hg : g * gi = 1) (d : Fin 2 → ℝ)
    (hker : g 2 0 * d 0 + g 2 1 * d 1 = 0) (s : ℝ) :
    conjU g gi d s 2 0 = 0 ∧ conjU g gi d s 2 1 = 0 ∧ conjU g gi d s 2 2 = 1 := by
  have e : ∀ j, (g * gi) 2 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j := fun j => by rw [hg]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e0 e1 e2
  simp at e0 e1 e2
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [conjU, nmat, transMat, Matrix.mul_apply, Fin.sum_univ_three]
    first
    | linear_combination e0 + s * gi 2 0 * hker
    | linear_combination e1 + s * gi 2 1 * hker
    | linear_combination e2 + s * gi 2 2 * hker

theorem eq_parabolicMatrix_of_bottom (X : Matrix (Fin 3) (Fin 3) ℝ) (h0 : X 2 0 = 0)
    (h1 : X 2 1 = 0) (h2 : X 2 2 = 1) : X = parabolicMatrix (topBlock X) (sideVec X) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parabolicMatrix, topBlock, sideVec, h0, h1, h2]

theorem topBlock_conjU (g gi : Matrix (Fin 3) (Fin 3) ℝ) (hg : g * gi = 1) (d : Fin 2 → ℝ)
    (s : ℝ) :
    topBlock (conjU g gi d s) = 1 + s • Matrix.vecMulVec (fun i : Fin 2 => g i.castSucc 0 * d 0 +
      g i.castSucc 1 * d 1) (fun j : Fin 2 => gi 2 j.castSucc) := by
  have e : ∀ i j, (g * gi) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by rw [hg]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e00 e01 e10 e11
  simp at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topBlock, conjU, nmat, transMat, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.vecMulVec] <;>
    first
    | linear_combination e00
    | linear_combination e01
    | linear_combination e10
    | linear_combination e11

/-- The `h`-independent factor of a coefficient of the summand. -/
def Kfun (n : ℕ) (G : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) : ℂ :=
  theta (planeAct G) x i j *
    ((∑ l : Fin 3, C (∑ k : Fin 3, seedRow (planeAct G x) k * (G k l : ℂ)) * X l :
      MvPolynomial (Fin 3) ℂ) ^ n).coeff m

/-- **The summand is pointwise linear in `h`**: its coefficients are `h(τ*) × K`. -/
theorem coeff_summandPoly_eq (n : ℕ) (h : ℂ → ℂ) {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1)
    (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (summandPoly n h G x i j).coeff m = h (seedTau (planeAct G x)) * Kfun n G x i j m := by
  rw [summandPoly_eq n h hG, MvPolynomial.coeff_C_mul, scalarPullback_seedForm0, Kfun, mul_assoc]

theorem seedTau_im_pos {p : Fin 5 → ℝ} (hp : p ∈ Omega) : 0 < (seedTau p).im := by
  simpa [seedTau] using hp.1

/-- Integer facts about the bottom row data of `γ` and the direction `d'`. -/
theorem geom_integer_facts (γ : SL(3, ℤ)) (hr : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 ∨
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 ≠ 0)
    (d' : Fin 2 → ℤ) (hd' : d' ≠ 0)
    (hker : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 * d' 0 + (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 * d' 1 = 0) :
    let a : Fin 2 → ℤ := fun i => (γ : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 0 * d' 0 +
      (γ : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 1 * d' 1
    let b : Fin 2 → ℤ := fun j => ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc
    a ≠ 0 ∧ b ≠ 0 ∧ a 0 * b 0 + a 1 * b 1 = 0 := by
  intro a b
  set M : Matrix (Fin 3) (Fin 3) ℤ := (γ : Matrix (Fin 3) (Fin 3) ℤ) with hM
  set Mi : Matrix (Fin 3) (Fin 3) ℤ := ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) with hMi
  have h2 : Mi * M = 1 := by
    rw [hM, hMi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have f20 : Mi 2 0 * M 0 0 + Mi 2 1 * M 1 0 + Mi 2 2 * M 2 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 2) 0
  have f21 : Mi 2 0 * M 0 1 + Mi 2 1 * M 1 1 + Mi 2 2 * M 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 2) 1
  have f22 : Mi 2 0 * M 0 2 + Mi 2 1 * M 1 2 + Mi 2 2 * M 2 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 2) 2
  have g00 : Mi 0 0 * M 0 0 + Mi 0 1 * M 1 0 + Mi 0 2 * M 2 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 0) 0
  have g01 : Mi 0 0 * M 0 1 + Mi 0 1 * M 1 1 + Mi 0 2 * M 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 0) 1
  have g10 : Mi 1 0 * M 0 0 + Mi 1 1 * M 1 0 + Mi 1 2 * M 2 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 1) 0
  have g11 : Mi 1 0 * M 0 1 + Mi 1 1 * M 1 1 + Mi 1 2 * M 2 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 1) 1
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have a0 : M 0 0 * d' 0 + M 0 1 * d' 1 = 0 := congrFun h0 0
    have a1 : M 1 0 * d' 0 + M 1 1 * d' 1 = 0 := congrFun h0 1
    apply hd'
    funext i
    fin_cases i
    · show d' 0 = 0
      linear_combination (Mi 0 0) * a0 + (Mi 0 1) * a1 + (Mi 0 2) * hker - d' 0 * g00 - d' 1 * g01
    · show d' 1 = 0
      linear_combination (Mi 1 0) * a0 + (Mi 1 1) * a1 + (Mi 1 2) * hker - d' 0 * g10 - d' 1 * g11
  · intro h0
    have b0 : Mi 2 0 = 0 := congrFun h0 0
    have b1 : Mi 2 1 = 0 := congrFun h0 1
    have h22 : Mi 2 2 ≠ 0 := by
      intro h
      rw [h, b0, b1] at f22
      simp at f22
    rcases hr with hr | hr
    · apply hr
      have : Mi 2 2 * M 2 0 = 0 := by rw [b0, b1] at f20; linear_combination f20
      exact (mul_eq_zero.mp this).resolve_left h22
    · apply hr
      have : Mi 2 2 * M 2 1 = 0 := by rw [b0, b1] at f21; linear_combination f21
      exact (mul_eq_zero.mp this).resolve_left h22
  · show (M 0 0 * d' 0 + M 0 1 * d' 1) * Mi 2 0 + (M 1 0 * d' 0 + M 1 1 * d' 1) * Mi 2 1 = 0
    linear_combination (d' 0) * f20 + (d' 1) * f21 - (Mi 2 2) * hker

/-- **The closed-direction integral vanishes**: for a non-identity bottom row and `d' ∈ ℤ²` in the
kernel of its first two entries, the integral over one period of the stabilizing direction of every
coefficient of `S_h(γ n(v + s N d'))(x)` is zero (cuspidality). -/
theorem closed_direction_zero (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (γ : SL(3, ℤ))
    (hr : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 ∨ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 ≠ 0)
    (d' : Fin 2 → ℤ) (hd' : d' ≠ 0)
    (hker : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 * d' 0 + (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 * d' 1 = 0)
    (v : Fin 2 → ℝ) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ∫ s in (0 : ℝ)..1, (summandPoly n (hfun f) (realMat γ * nmat (v + s • ((N : ℝ) • intVec d')))
      x i j).coeff m = 0 := by
  obtain ⟨ha', hb', hab⟩ := geom_integer_facts γ hr d' hd' hker
  set a' : Fin 2 → ℤ := fun i => (γ : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 0 * d' 0 +
      (γ : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 1 * d' 1 with ha'def
  set b' : Fin 2 → ℤ := fun j => ((γ⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc
    with hb'def
  obtain ⟨B, μ', hμ'0, hmat⟩ := rankOne_normalForm a' b' ha' hb' hab
  set g := realMat γ with hgdef
  set gi := realMat γ⁻¹ with higdef
  have hg1 : g * gi = 1 := by rw [hgdef, higdef, ← realMat_mul, mul_inv_cancel, realMat_one]
  have hg2 : gi * g = 1 := by rw [hgdef, higdef, ← realMat_mul, inv_mul_cancel, realMat_one]
  have hgdet : g.det = 1 := det_realMat γ
  set D : Fin 2 → ℝ := (N : ℝ) • intVec d' with hD
  have hkerR : g 2 0 * D 0 + g 2 1 * D 1 = 0 := by
    have : ((((γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 * d' 0 + (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 * d' 1 :
      ℤ)) : ℝ) = 0 := by rw [hker]; simp
    simp only [hD, hgdef, realMat_apply, intVec, Pi.smul_apply, smul_eq_mul]
    push_cast at this
    linear_combination (N : ℝ) * this
  set G := g * nmat v with hG
  have hGdet : G.det = 1 := by rw [hG, Matrix.det_mul, hgdet, det_nmat]; norm_num
  have hμ : (N : ℤ) ∣ (N : ℤ) * μ' := dvd_mul_right _ _
  have hμ0 : (N : ℤ) * μ' ≠ 0 := mul_ne_zero (by exact_mod_cast NeZero.ne N) hμ'0
  have hxτ := seedTau_im_pos (planeAct_mem hGdet hx)
  have key : ∀ s : ℝ, (summandPoly n (hfun f) (g * nmat (v + s • D)) x i j).coeff m =
      slashTwisted (n + 3) (unipConj B (((N : ℤ) * μ' : ℤ) * s)) (hfun f)
        (seedTau (planeAct G x)) * Kfun n G x i j m := by
    intro s
    have hbot := conjU_bottom g gi hg1 D hkerR s
    have hpar := eq_parabolicMatrix_of_bottom (conjU g gi D s) hbot.1 hbot.2.1 hbot.2.2
    have hdetA : (topBlock (conjU g gi D s)).det = 1 := by
      have h1 := det_conjU g gi hgdet hg2 D s
      rw [hpar, SeedC3.det_parabolicMatrix] at h1
      exact h1
    have hblock : topBlock (conjU g gi D s) = unipConj B (((N : ℤ) * μ' : ℤ) * s) := by
      rw [topBlock_conjU g gi hg1 D s, unipConj_eq]
      congr 1
      have hcast : Matrix.vecMulVec (fun i : Fin 2 => g i.castSucc 0 * D 0 + g i.castSucc 1 * D 1)
          (fun j : Fin 2 => gi 2 j.castSucc) =
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
    rw [← conjU_mul g gi hg2 D v s, hpar,
      summandPoly_parabolic_mul n (hfun f) (topBlock (conjU g gi D s)) hdetA _ hGdet hx i j,
      coeff_summandPoly_eq n _ hGdet, hblock]
  simp_rw [key]
  rw [intervalIntegral.integral_mul_const,
    integral_unipConj_zero N n f B _ hμ0 hμ _ hxτ, zero_mul]

end TernaryPeriodPolynomials.Argument.EisensteinClass
