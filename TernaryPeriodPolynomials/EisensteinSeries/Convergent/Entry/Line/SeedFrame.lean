module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SeedCovariance

@[expose] public section


/-!
# Covariance of the line seed under the line parabolic (R3 of the ML4b reduction)

For `q = [[a, bᵀ], [0, C]]` with `a > 0`, `det C > 0`, and invertible `g`, the frame coefficient of the
line seed `σ_h = h(τ)(τZ - Y)ⁿ (τ dw₁ + dw₂) ∧ dτ` satisfies
`σ̃_h(q g)(V, W) = (a² / det C) · σ̃_{h|C}(g)(V, W)` with `h|C = slashTwisted (n+3) C h`
(`lineFrameCoefficient_lineParabolic`). Ingredients: the closed form of the line seed's frame
coefficient (`lineFrameCoefficient_lineSeedForm`), the chain rule for the line-chart tangents
(`lineTangent_lineParabolic`: `dw' = a dw C⁻¹`, `dτ' = det C/(cτ+d)² dτ`), and the action of `ρ(q)⁻¹`
on `(τ'Z - Y)ⁿ` (`rho_inv_lineParabolic_pow`). Step R3 of K's reduction of the form identity of
Appendix C.5 (`ar:sec:real`) to the base point.

Written by Claude Opus 5.5.
-/

open MvPolynomial Matrix Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

/-- `β = τ dw₁ + dw₂` on a line-face tangent vector. -/
def lineBeta (τ : ℂ) (v : Fin 5 → ℝ) : ℂ := τ * v 0 + v 1

/-- `dτ` on a line-face tangent vector. -/
def lineDTauOf (v : Fin 5 → ℝ) : ℂ := (v 2 : ℂ) + Complex.I * v 3

/-- The line seed's frame coefficient in closed form. -/
theorem lineFrameCoefficient_lineSeedForm (n : ℕ) (h : ℂ → ℂ) (g V W : Matrix (Fin 3) (Fin 3) ℝ) :
    lineFrameCoefficient (lineSeedForm n h) g V W =
      SeedC3.rho g⁻¹ (C (h (lineTau (lineChart (g * g.transpose))) *
        (lineBeta (lineTau (lineChart (g * g.transpose))) (lineTangent g V) *
            lineDTauOf (lineTangent g W) -
          lineBeta (lineTau (lineChart (g * g.transpose))) (lineTangent g W) *
            lineDTauOf (lineTangent g V))) *
        (C (lineTau (lineChart (g * g.transpose))) * X 2 - X 1) ^ n) := by
  unfold lineFrameCoefficient
  congr 1
  simp only [lineSeedForm, Fin.sum_univ_five, seedDTau, lineBeta, lineDTauOf,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  simp only [map_mul, map_sub, map_add, map_zero, map_neg, map_one, mul_one, one_mul,
    mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, Complex.ofReal_mul]
  ring

/-- `ρ` commutes with constants. -/
theorem rho_C_mul (M : Matrix (Fin 3) (Fin 3) ℝ) (x : ℂ) (P : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho M (C x * P) = C x * SeedC3.rho M P := by
  unfold SeedC3.rho
  rw [map_mul, bind₁_C_right]
  ring

theorem det_lineParabolic (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) :
    (lineParabolic a b C).det = a * C.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [lineParabolic]
  ring

theorem gramCurve_lineParabolic_mul (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (g V : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) :
    gramCurve (lineParabolic a b C * g) V ε = lineConj a b C (gramCurve g V ε) := by
  unfold gramCurve lineConj
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem gram_lineParabolic_mul (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (g : Matrix (Fin 3) (Fin 3) ℝ) :
    (lineParabolic a b C * g) * (lineParabolic a b C * g).transpose =
      lineConj a b C (g * g.transpose) := by
  unfold lineConj
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- `ρ(q)⁻¹` on the line-seed linear form. -/
theorem rho_inv_lineParabolic_pow (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hq : (lineParabolic a b C).det ≠ 0) (σ : ℂ) (n : ℕ) :
    SeedC3.rho (lineParabolic a b C)⁻¹ ((MvPolynomial.C σ * X 2 - X 1) ^ n) =
      MvPolynomial.C (((a * C.det : ℝ) : ℂ)) *
        (MvPolynomial.C (σ * C 1 0 - C 0 0) * X 1 + MvPolynomial.C (σ * C 1 1 - C 0 1) * X 2) ^ n := by
  have hu : IsUnit (lineParabolic a b C).det := isUnit_iff_ne_zero.mpr hq
  unfold SeedC3.rho
  rw [Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv,
    det_lineParabolic]
  rw [map_pow, map_sub, map_mul, bind₁_C_right, bind₁_X_right, bind₁_X_right]
  simp only [Fin.sum_univ_three, lineParabolic, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  simp only [Complex.ofReal_zero, map_zero, zero_mul, zero_add, Complex.ofReal_mul, map_mul,
    map_sub]
  congr 1
  ring

/-! ### The tangent vectors of the line chart -/

private theorem hd (g V : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    DifferentiableAt ℝ (fun ε => gramCurve g V ε i j) 0 :=
  (hasDerivAt_gramCurve g V i j).differentiableAt

private theorem gram_at_zero_pos (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    0 < gramCurve g V 0 2 2 ∧
      0 < gramCurve g V 0 1 1 * gramCurve g V 0 2 2 - gramCurve g V 0 1 2 * gramCurve g V 0 2 1 := by
  rw [gramCurve_zero]
  refine ⟨gram_pos_22 g hg, ?_⟩
  have h := gram_minor_pos g hg
  have h21 : (g * g.transpose) 2 1 = (g * g.transpose) 1 2 := (gram_isSymm g).apply 1 2
  rw [h21, ← sq]
  exact h

private theorem lineChart_differentiableAt (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0)
    (i : Fin 5) (hi : i ≠ 4) :
    DifferentiableAt ℝ (fun ε => lineChart (gramCurve g V ε) i) 0 := by
  obtain ⟨h22, hB⟩ := gram_at_zero_pos g V hg
  have hBd : DifferentiableAt ℝ (fun ε => gramCurve g V ε 1 1 * gramCurve g V ε 2 2 -
      gramCurve g V ε 1 2 * gramCurve g V ε 2 1) 0 :=
    ((hd g V 1 1).mul (hd g V 2 2)).sub ((hd g V 1 2).mul (hd g V 2 1))
  fin_cases i
  · exact (((hd g V 0 1).mul (hd g V 2 2)).sub ((hd g V 0 2).mul (hd g V 2 1))).div hBd hB.ne'
  · exact (((hd g V 0 2).mul (hd g V 1 1)).sub ((hd g V 0 1).mul (hd g V 1 2))).div hBd hB.ne'
  · exact (hd g V 1 2).div (hd g V 2 2) h22.ne'
  · exact (hBd.sqrt hB.ne').div (hd g V 2 2) h22.ne'
  · exact absurd rfl hi

private theorem hasDerivAt_lineChart (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0)
    (i : Fin 5) (hi : i ≠ 4) :
    HasDerivAt (fun ε => lineChart (gramCurve g V ε) i) (lineTangent g V i) 0 :=
  (lineChart_differentiableAt g V hg i hi).hasDerivAt

private theorem eventually_gram_pos (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < gramCurve g V ε 2 2 ∧
      0 < gramCurve g V ε 1 1 * gramCurve g V ε 2 2 - gramCurve g V ε 1 2 * gramCurve g V ε 2 1 := by
  obtain ⟨h22, hB⟩ := gram_at_zero_pos g V hg
  have c22 : ContinuousAt (fun ε => gramCurve g V ε 2 2) 0 := (hd g V 2 2).continuousAt
  have cB : ContinuousAt (fun ε => gramCurve g V ε 1 1 * gramCurve g V ε 2 2 -
      gramCurve g V ε 1 2 * gramCurve g V ε 2 1) 0 :=
    (((hd g V 1 1).mul (hd g V 2 2)).sub ((hd g V 1 2).mul (hd g V 2 1))).continuousAt
  exact (continuousAt_const.eventually_lt c22 h22).and (continuousAt_const.eventually_lt cB hB)

/-- The Möbius derivative. -/
theorem hasDerivAt_mobius (C : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℂ)
    (hden : (C 1 0 : ℂ) * τ + C 1 1 ≠ 0) :
    HasDerivAt (mobius C) ((C.det : ℂ) / ((C 1 0 : ℂ) * τ + C 1 1) ^ 2) τ := by
  have h1 : HasDerivAt (fun z : ℂ => (C 0 0 : ℂ) * z + C 0 1) (C 0 0 : ℂ) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (C 0 0 : ℂ)).add_const (C 0 1 : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => (C 1 0 : ℂ) * z + C 1 1) (C 1 0 : ℂ) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (C 1 0 : ℂ)).add_const (C 1 1 : ℂ)
  refine (h1.div h2 hden).congr_deriv ?_
  rw [Matrix.det_fin_two]
  push_cast
  ring

/-- The `τ` of a positive Gram matrix lies in the upper half plane. -/
theorem lineTau_im_pos (G : Matrix (Fin 3) (Fin 3) ℝ) (h22 : 0 < G 2 2)
    (hB : 0 < G 1 1 * G 2 2 - G 1 2 * G 2 1) : 0 < (lineTau (lineChart G)).im := by
  simp only [lineTau, lineChart, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_cons, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact div_pos (Real.sqrt_pos.mpr hB) h22

theorem mobius_den_ne_zero (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : C.det ≠ 0) (τ : ℂ)
    (hτ : 0 < τ.im) : (C 1 0 : ℂ) * τ + C 1 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.zero_im, mul_eq_zero, Complex.add_re, Complex.mul_re, sub_zero,
    Complex.zero_re] at him hre
  have hc : C 1 0 = 0 := him.resolve_right hτ.ne'
  rw [hc, zero_mul, zero_add] at hre
  apply hC
  rw [Matrix.det_fin_two, hc, hre]
  ring

/-- **The line-chart tangent at `q g`.** -/
theorem lineTangent_lineParabolic (a : ℝ) (b : Fin 2 → ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : 0 < C.det) (g V : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) :
    lineTangent (lineParabolic a b C * g) V 0 =
        ((a * lineTangent g V 0) * C 1 1 - (a * lineTangent g V 1) * C 1 0) / C.det ∧
      lineTangent (lineParabolic a b C * g) V 1 =
        ((a * lineTangent g V 1) * C 0 0 - (a * lineTangent g V 0) * C 0 1) / C.det ∧
      lineDTauOf (lineTangent (lineParabolic a b C * g) V) =
        (C.det : ℂ) / ((C 1 0 : ℂ) * lineTau (lineChart (g * g.transpose)) + C 1 1) ^ 2 *
          lineDTauOf (lineTangent g V) := by
  have hp : ∀ i : Fin 5, i ≠ 4 →
      HasDerivAt (fun ε => lineChart (gramCurve g V ε) i) (lineTangent g V i) 0 :=
    fun i hi => hasDerivAt_lineChart g V hg i hi
  have hev := eventually_gram_pos g V hg
  have hcurve : ∀ ε, gramCurve (lineParabolic a b C * g) V ε =
      lineConj a b C (gramCurve g V ε) := gramCurve_lineParabolic_mul a b C g V
  -- the `w` coordinates
  have hw : ∀ᶠ ε in 𝓝 (0 : ℝ),
      lineChart (gramCurve (lineParabolic a b C * g) V ε) 0 =
          ((a * lineChart (gramCurve g V ε) 0 + b 0) * C 1 1 -
            (a * lineChart (gramCurve g V ε) 1 + b 1) * C 1 0) / C.det ∧
        lineChart (gramCurve (lineParabolic a b C * g) V ε) 1 =
          ((a * lineChart (gramCurve g V ε) 1 + b 1) * C 0 0 -
            (a * lineChart (gramCurve g V ε) 0 + b 0) * C 0 1) / C.det := by
    filter_upwards [hev] with ε hε
    rw [hcurve]
    exact lineChart_lineConj_w a b C hC.ne' _ (gramCurve_isSymm g V ε) hε.2.ne'
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have hd0 : HasDerivAt (fun ε => lineChart (gramCurve (lineParabolic a b C * g) V ε) 0)
      (((a * lineTangent g V 0) * C 1 1 - (a * lineTangent g V 1) * C 1 0) / C.det) 0 := by
    have := ((((h0.const_mul a).add_const (b 0)).mul_const (C 1 1)).sub
      (((h1.const_mul a).add_const (b 1)).mul_const (C 1 0))).div_const C.det
    exact this.congr_of_eventuallyEq (hw.mono fun ε hε => hε.1)
  have hd1 : HasDerivAt (fun ε => lineChart (gramCurve (lineParabolic a b C * g) V ε) 1)
      (((a * lineTangent g V 1) * C 0 0 - (a * lineTangent g V 0) * C 0 1) / C.det) 0 := by
    have := ((((h1.const_mul a).add_const (b 1)).mul_const (C 0 0)).sub
      (((h0.const_mul a).add_const (b 0)).mul_const (C 0 1))).div_const C.det
    exact this.congr_of_eventuallyEq (hw.mono fun ε hε => hε.2)
  refine ⟨hd0.deriv, hd1.deriv, ?_⟩
  -- the `τ` coordinate
  have hτ : HasDerivAt (fun ε => lineTau (lineChart (gramCurve g V ε)))
      (lineDTauOf (lineTangent g V)) 0 := by
    have h2 := (hp 2 (by decide)).ofReal_comp
    have h3 := ((hp 3 (by decide)).ofReal_comp).const_mul Complex.I
    exact h2.add h3
  obtain ⟨h22, hB⟩ := gram_at_zero_pos g V hg
  have hτ0 : lineTau (lineChart (gramCurve g V 0)) = lineTau (lineChart (g * g.transpose)) := by
    rw [gramCurve_zero]
  have hden : (C 1 0 : ℂ) * lineTau (lineChart (g * g.transpose)) + C 1 1 ≠ 0 := by
    apply mobius_den_ne_zero C hC.ne'
    rw [← hτ0]
    exact lineTau_im_pos _ h22 hB
  have hmob := hasDerivAt_mobius C _ hden
  rw [← hτ0] at hmob
  have hcomp := hmob.comp (0 : ℝ) hτ
  have hev' : (fun ε => lineTau (lineChart (gramCurve (lineParabolic a b C * g) V ε))) =ᶠ[𝓝 0]
      (mobius C ∘ fun ε => lineTau (lineChart (gramCurve g V ε))) := by
    filter_upwards [hev] with ε hε
    rw [hcurve, Function.comp_apply]
    exact lineTau_lineConj a b C hC _ (gramCurve_isSymm g V ε) hε.1 hε.2
  have hT := hcomp.congr_of_eventuallyEq hev'
  rw [hτ0] at hT
  set D := (C.det : ℂ) / ((C 1 0 : ℂ) * lineTau (lineChart (g * g.transpose)) + C 1 1) ^ 2 *
    lineDTauOf (lineTangent g V) with hD
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hT
  have him := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hT
  have e2 : (fun ε => lineChart (gramCurve (lineParabolic a b C * g) V ε) 2) =
      (⇑Complex.reCLM ∘ fun ε => lineTau (lineChart (gramCurve (lineParabolic a b C * g) V ε))) := by
    funext ε
    simp [lineTau]
  have e3 : (fun ε => lineChart (gramCurve (lineParabolic a b C * g) V ε) 3) =
      (⇑Complex.imCLM ∘ fun ε => lineTau (lineChart (gramCurve (lineParabolic a b C * g) V ε))) := by
    funext ε
    simp [lineTau]
  have t2 : lineTangent (lineParabolic a b C * g) V 2 = D.re := by
    unfold lineTangent
    rw [e2]
    exact hre.deriv
  have t3 : lineTangent (lineParabolic a b C * g) V 3 = D.im := by
    unfold lineTangent
    rw [e3]
    exact him.deriv
  rw [lineDTauOf, t2, t3, mul_comm]
  exact Complex.re_add_im D

/-- `β` at `q g`: `β' = a/(cτ+d) β`. -/
private theorem lineBeta_transform (a : ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : C.det ≠ 0) (τ : ℂ)
    (hden : (C 1 0 : ℂ) * τ + C 1 1 ≠ 0) (t0 t1 : ℝ) :
    mobius C τ * (((((a * t0) * C 1 1 - (a * t1) * C 1 0) / C.det : ℝ)) : ℂ) +
        ((((a * t1) * C 0 0 - (a * t0) * C 0 1) / C.det : ℝ) : ℂ) =
      (a : ℂ) / ((C 1 0 : ℂ) * τ + C 1 1) * (τ * t0 + t1) := by
  have hΔ : ((C.det : ℝ) : ℂ) = (C 0 0 : ℂ) * C 1 1 - C 0 1 * C 1 0 := by
    rw [Matrix.det_fin_two]; push_cast; ring
  have hΔne : ((C.det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hC
  have hden' : τ * (C 1 0 : ℂ) + C 1 1 ≠ 0 := by rwa [mul_comm]
  unfold mobius
  push_cast
  rw [hΔ] at hΔne ⊢
  field_simp
  ring

/-- **R3 (line seed: `M_Q`/`N_Q`-covariance, pointwise).** -/
theorem lineFrameCoefficient_lineParabolic (n : ℕ) (h : ℂ → ℂ) (a : ℝ) (b : Fin 2 → ℝ)
    (C : Matrix (Fin 2) (Fin 2) ℝ) (ha : 0 < a) (hC : 0 < C.det) (g V W : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : g.det ≠ 0) :
    lineFrameCoefficient (lineSeedForm n h) (lineParabolic a b C * g) V W =
      MvPolynomial.C (((a ^ 2 / C.det : ℝ)) : ℂ) *
        lineFrameCoefficient (lineSeedForm n (slashTwisted (n + 3) C h)) g V W := by
  have h22 := gram_pos_22 g hg
  have hB : 0 < (g * g.transpose) 1 1 * (g * g.transpose) 2 2 -
      (g * g.transpose) 1 2 * (g * g.transpose) 2 1 := by
    have h21 : (g * g.transpose) 2 1 = (g * g.transpose) 1 2 := (gram_isSymm g).apply 1 2
    rw [h21, ← sq]; exact gram_minor_pos g hg
  have hq : (lineParabolic a b C).det ≠ 0 := by
    rw [det_lineParabolic]; exact mul_ne_zero ha.ne' hC.ne'
  set τ := lineTau (lineChart (g * g.transpose)) with hτdef
  have hτ' : lineTau (lineChart ((lineParabolic a b C * g) * (lineParabolic a b C * g).transpose)) =
      mobius C τ := by
    rw [gram_lineParabolic_mul]
    exact lineTau_lineConj a b C hC _ (gram_isSymm g) h22 hB
  have hden : (C 1 0 : ℂ) * τ + C 1 1 ≠ 0 :=
    mobius_den_ne_zero C hC.ne' τ (lineTau_im_pos _ h22 hB)
  obtain ⟨v0, v1, vD⟩ := lineTangent_lineParabolic a b C hC g V hg
  obtain ⟨w0, w1, wD⟩ := lineTangent_lineParabolic a b C hC g W hg
  rw [← hτdef] at vD wD
  rw [lineFrameCoefficient_lineSeedForm, lineFrameCoefficient_lineSeedForm, hτ', ← hτdef,
    Matrix.mul_inv_rev, rho_mul, rho_C_mul, rho_inv_lineParabolic_pow a b C hq, ← rho_C_mul]
  congr 1
  have hden' : τ * (C 1 0 : ℂ) + C 1 1 ≠ 0 := by rwa [mul_comm]
  have hlin : MvPolynomial.C (mobius C τ * C 1 0 - C 0 0) * X 1 +
      MvPolynomial.C (mobius C τ * C 1 1 - C 0 1) * X 2 =
        MvPolynomial.C ((C.det : ℂ) / ((C 1 0 : ℂ) * τ + C 1 1)) *
          (MvPolynomial.C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) := by
    have e1 : mobius C τ * C 1 0 - C 0 0 = -((C.det : ℂ) / ((C 1 0 : ℂ) * τ + C 1 1)) := by
      unfold mobius; rw [Matrix.det_fin_two]; push_cast; field_simp; ring
    have e2 : mobius C τ * C 1 1 - C 0 1 = (C.det : ℂ) / ((C 1 0 : ℂ) * τ + C 1 1) * τ := by
      unfold mobius; rw [Matrix.det_fin_two]; push_cast; field_simp; ring
    rw [e1, e2, map_neg, map_mul]
    ring
  rw [hlin]
  have eL : ∀ x y z : ℂ, MvPolynomial.C x * (MvPolynomial.C y *
      (MvPolynomial.C z * (MvPolynomial.C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ)) ^ n) =
        MvPolynomial.C (x * y * z ^ n) * (MvPolynomial.C τ * X 2 - X 1) ^ n := by
    intro x y z
    rw [mul_pow, ← map_pow]
    simp only [map_mul]
    ring
  rw [eL, ← mul_assoc, ← map_mul]
  congr 2
  -- the scalar identity
  simp only [lineBeta, lineDTauOf] at vD wD ⊢
  rw [v0, v1, w0, w1, vD, wD]
  rw [lineBeta_transform a C hC.ne' τ hden, lineBeta_transform a C hC.ne' τ hden]
  unfold slashTwisted
  have hΔne : ((C.det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [zpow_neg, zpow_natCast]
  rw [show ((C 0 0 : ℂ) * τ + C 0 1) / ((C 1 0 : ℂ) * τ + C 1 1) = mobius C τ from rfl]
  generalize h (mobius C τ) = hv
  push_cast
  generalize (C 1 0 : ℂ) * τ + C 1 1 = dd at hden ⊢
  simp only [div_pow]
  field_simp
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
