module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityTangent
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.MeanValuePolar

@[expose] public section


/-!
# The base-point integrand in the disc variable `ξ`

For `(s,t) ≠ 0` put `r = √(1+s²+t²)` and `ξ = xiOf s t = (t + i s)/(r + 1)` (`|ξ| < 1`, `ξ² = (τ-i)/(τ+i)`).
Then `s, t, τ = entryTau (s,t)` and the coefficients `a, b` of the transported seed polynomial are the rational
functions of `(r, ξ)` of `FormIdentityWedge` (`s_eq_sOf`, `t_eq_tOf`, `tau_eq_tauOf`, `coefA_mul`, `coefB_mul`), and for
arbitrary symmetric directions `p, p'` the wedge of the two tangent symbols is
`wedgeSym_dirSymC_closed : I/(2r³) · wedgePoly p p' ξ / (1-ξ²)³` with `wedgePoly` a polynomial in `ξ`
(a bilinear combination of the fifteen closed forms of `FormIdentityWedge`).

`coeff_frameCoefficient_xi`: for every monomial `m` of degree `n`,
`coeff_m (ω̃_h(L_{s,t})(V,W)) = K_m(r) · F(ξ²) · xiPoly m ξ · wedgePoly (V+Vᵀ) (W+Wᵀ) ξ`,
`K_m(r) = multinomial(m) (i/2) (2i)^{-(n+3)} r^{-(n+3)}`, `F = entryDiscFn n h` the disc function of `h`.
Since `xiPoly` and `wedgePoly` are polynomials in `ξ`, the mean-value property of `F(ξ²)` evaluates the
angular integral at `ξ = 0`.

Formalized by Claude Sonnet 5.5.  The multipliers of the `linear_combination`
proofs modulo `r² = 1+s²+t²`, `i² = -1` were found with a small exact-arithmetic script.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open Complex MvPolynomial TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryCoefficient

/-- `dirSym` with complex `s, t`. -/
def dirSymC (p : Matrix (Fin 3) (Fin 3) ℝ) (s t τ : ℂ) : Symbols where
  psi := ((p 0 1 : ℂ) - τ * p 0 2) + ((p 1 1 : ℂ) * s + p 1 2 * t) - τ * ((p 1 2 : ℂ) * s + p 2 2 * t)
  pi := (p 1 1 : ℂ) - 2 * τ * p 1 2 + τ ^ 2 * p 2 2
  d := (p 0 0 : ℂ) + 2 * ((p 0 1 : ℂ) * s + p 0 2 * t) + p 1 1 * s ^ 2 + 2 * p 1 2 * s * t + p 2 2 * t ^ 2

theorem dirSym_eq_dirSymC (p : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (τ : ℂ) :
    dirSym p s t τ = dirSymC p (s : ℂ) (t : ℂ) τ := rfl

/-- The coefficients `(p₀₀, p₁₁, p₂₂, p₀₁, p₀₂, p₁₂)` of a symmetric direction. -/
def dirCoef (p : Matrix (Fin 3) (Fin 3) ℝ) : Fin 6 → ℂ :=
  ![p 0 0, p 1 1, p 2 2, p 0 1, p 0 2, p 1 2]

/-- The antisymmetric coefficient `w_{ab} = pₐ p'_b - p'ₐ p_b`. -/
def dirW (p p' : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 6) : ℂ :=
  dirCoef p a * dirCoef p' b - dirCoef p' a * dirCoef p b

theorem wedgeSym_expand (r s t τ : ℂ) (p p' : Matrix (Fin 3) (Fin 3) ℝ) :
    wedgeSym r s t τ (dirSymC p s t τ) (dirSymC p' s t τ) =
      dirW p p' 0 1 * wedgeSym r s t τ sym00 (sym11 s) +
      dirW p p' 0 2 * wedgeSym r s t τ sym00 (sym22 t τ) +
      dirW p p' 0 3 * wedgeSym r s t τ sym00 (sym01 s) +
      dirW p p' 0 4 * wedgeSym r s t τ sym00 (sym02 t τ) +
      dirW p p' 0 5 * wedgeSym r s t τ sym00 (sym12 s t τ) +
      dirW p p' 1 2 * wedgeSym r s t τ (sym11 s) (sym22 t τ) +
      dirW p p' 1 3 * wedgeSym r s t τ (sym11 s) (sym01 s) +
      dirW p p' 1 4 * wedgeSym r s t τ (sym11 s) (sym02 t τ) +
      dirW p p' 1 5 * wedgeSym r s t τ (sym11 s) (sym12 s t τ) +
      dirW p p' 2 3 * wedgeSym r s t τ (sym22 t τ) (sym01 s) +
      dirW p p' 2 4 * wedgeSym r s t τ (sym22 t τ) (sym02 t τ) +
      dirW p p' 2 5 * wedgeSym r s t τ (sym22 t τ) (sym12 s t τ) +
      dirW p p' 3 4 * wedgeSym r s t τ (sym01 s) (sym02 t τ) +
      dirW p p' 3 5 * wedgeSym r s t τ (sym01 s) (sym12 s t τ) +
      dirW p p' 4 5 * wedgeSym r s t τ (sym02 t τ) (sym12 s t τ) := by
  simp only [wedgeSym, dirSymC, dirW, dirCoef, sym00, sym01, sym02, sym11, sym12, sym22,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  ring


/-- The numerator polynomial `P(p, p'; ξ) = Σ_{a<b} w_{ab} N_{ab}(ξ) (1-ξ²)³`. -/
def wedgePoly (p p' : Matrix (Fin 3) (Fin 3) ℝ) (ξ : ℂ) : ℂ :=
  dirW p p' 0 1 * (2 * I * (ξ + ξ ^ 3) * (1 - ξ ^ 2)) +
  dirW p p' 0 2 * (-2 * I * (ξ + ξ ^ 3) * (1 - ξ ^ 2)) +
  dirW p p' 0 3 * (-4 * ξ ^ 2 * (1 - ξ ^ 2)) + dirW p p' 0 4 * (4 * I * (ξ ^ 2 + ξ ^ 4)) +
  dirW p p' 0 5 * (4 * (ξ + ξ ^ 5)) +
  dirW p p' 1 2 * (2 * I * (ξ + ξ ^ 3) * (1 - ξ ^ 2)) +
  dirW p p' 1 3 * (-(1 + ξ ^ 2) ^ 2 * (1 - ξ ^ 2)) +
  dirW p p' 1 4 * (I * (1 - 5 * ξ ^ 2 - 5 * ξ ^ 4 + ξ ^ 6)) +
  dirW p p' 1 5 * (-2 * ξ * (1 + ξ ^ 2) ^ 2) +
  dirW p p' 2 3 * ((1 + 6 * ξ ^ 2 + ξ ^ 4) * (1 - ξ ^ 2)) +
  dirW p p' 2 4 * (-I * (1 + ξ ^ 2) * (1 - ξ ^ 2) ^ 2) +
  dirW p p' 2 5 * (-2 * ξ * (1 - ξ ^ 2) ^ 2) + dirW p p' 3 4 * (16 * ξ ^ 3) +
  dirW p p' 3 5 * (-2 * I * (1 + ξ ^ 2) ^ 3) + dirW p p' 4 5 * (-2 * (1 - ξ ^ 2) ^ 3)

/-- **The wedge of two symmetric directions at the base point, in the variable `ξ`.** -/
theorem wedgeSym_dirSymC_closed (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0)
    (p p' : Matrix (Fin 3) (Fin 3) ℝ) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (dirSymC p (sOf r ξ) (tOf r ξ) (tauOf ξ))
        (dirSymC p' (sOf r ξ) (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (wedgePoly p p' ξ / (1 - ξ ^ 2) ^ 3) := by
  rw [wedgeSym_expand, wedge_00_11 r ξ hξ hw hr, wedge_00_22 r ξ hξ hw hr, wedge_00_01 r ξ hξ hw hr,
    wedge_00_02 r ξ hξ hw hr, wedge_00_12 r ξ hξ hw hr, wedge_11_22 r ξ hξ hw hr,
    wedge_11_01 r ξ hξ hw hr, wedge_11_02 r ξ hξ hw hr, wedge_11_12 r ξ hξ hw hr,
    wedge_22_01 r ξ hξ hw hr, wedge_22_02 r ξ hξ hw hr, wedge_22_12 r ξ hξ hw hr,
    wedge_01_02 r ξ hξ hw hr, wedge_01_12 r ξ hξ hw hr, wedge_02_12 r ξ hξ hw hr]
  unfold wedgePoly
  field_simp
  ring


/-- The disc variable `ξ = (t + i s)/(r + 1)` of the base point `L_{s,t}`. -/
def xiOf (s t : ℝ) : ℂ := ((t : ℂ) + I * s) / ((entryRadius (s, t) : ℂ) + 1)

theorem entryRadius_pos' (s t : ℝ) : 0 < entryRadius (s, t) := Real.sqrt_pos.mpr (by positivity)

theorem tPlusIs_ne (s t : ℝ) (h : (s, t) ≠ (0, 0)) : (t : ℂ) + I * s ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  simp at h1 h2
  simp [h1, h2]

theorem xiOf_ne_zero (s t : ℝ) (h : (s, t) ≠ (0, 0)) : xiOf s t ≠ 0 := by
  unfold xiOf
  have hr := entryRadius_pos' s t
  have : (entryRadius (s, t) : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : entryRadius (s, t) + 1 ≠ 0)
  exact div_ne_zero (tPlusIs_ne s t h) this

theorem norm_sq_tPlusIs (s t : ℝ) :
    ((t : ℂ) + I * s) * ((t : ℂ) - I * s) = (entryRadius (s, t) : ℂ) ^ 2 - 1 := by
  rw [entryRadius_sq_complex]
  linear_combination (-(s : ℂ) ^ 2) * Complex.I_sq

theorem s_eq_sOf (s t : ℝ) (h : (s, t) ≠ (0, 0)) :
    (s : ℂ) = sOf (entryRadius (s, t) : ℂ) (xiOf s t) := by
  have hz := tPlusIs_ne s t h
  have hr := entryRadius_pos' s t
  have hr1 : (entryRadius (s, t) : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : entryRadius (s, t) + 1 ≠ 0)
  have hn := norm_sq_tPlusIs s t
  have hz' : (s : ℂ) * I + t ≠ 0 := by rwa [add_comm, mul_comm]
  have hz'' : (t : ℂ) + s * I ≠ 0 := by rwa [mul_comm]
  unfold sOf xiOf
  field_simp
  linear_combination (-1 : ℂ) * hn

theorem t_eq_tOf (s t : ℝ) (h : (s, t) ≠ (0, 0)) :
    (t : ℂ) = tOf (entryRadius (s, t) : ℂ) (xiOf s t) := by
  have hz := tPlusIs_ne s t h
  have hr := entryRadius_pos' s t
  have hr1 : (entryRadius (s, t) : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : entryRadius (s, t) + 1 ≠ 0)
  have hn := norm_sq_tPlusIs s t
  have hz'' : (t : ℂ) + s * I ≠ 0 := by rwa [mul_comm]
  unfold tOf xiOf
  field_simp
  linear_combination hn


theorem norm_xiOf_lt_one (s t : ℝ) : ‖xiOf s t‖ < 1 := by
  have hr := entryRadius_pos' s t
  have hr2 : entryRadius (s, t) ^ 2 = 1 + s ^ 2 + t ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + s ^ 2 + t ^ 2 by positivity)
    unfold entryRadius; exact this
  unfold xiOf
  rw [norm_div]
  have hn : ‖(t : ℂ) + I * s‖ ^ 2 = t ^ 2 + s ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hden : ‖(entryRadius (s, t) : ℂ) + 1‖ = entryRadius (s, t) + 1 := by
    have : (entryRadius (s, t) : ℂ) + 1 = ((entryRadius (s, t) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hden, div_lt_one (by linarith)]
  have h0 : 0 ≤ ‖(t : ℂ) + I * s‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(t : ℂ) + I * s‖ - (entryRadius (s, t) + 1)), sq_nonneg s, sq_nonneg t]

theorem one_sub_xi_sq_ne (s t : ℝ) : 1 - xiOf s t ^ 2 ≠ 0 := by
  intro h0
  have h1 : xiOf s t ^ 2 = 1 := by linear_combination -h0
  have := congrArg norm h1
  rw [norm_pow, norm_one] at this
  have h2 := norm_xiOf_lt_one s t
  have h3 : 0 ≤ ‖xiOf s t‖ := norm_nonneg _
  nlinarith

theorem r1_sq_add_z_sq (s t : ℝ) :
    ((entryRadius (s, t) : ℂ) + 1) ^ 2 + ((t : ℂ) + I * s) ^ 2 =
      2 * (1 + (t : ℂ) ^ 2 + entryRadius (s, t) + t * s * I) := by
  linear_combination entryRadius_sq_complex s t + ((s : ℂ) ^ 2) * Complex.I_sq

theorem tau_eq_tauOf (s t : ℝ) :
    entryTau (s, t) = tauOf (xiOf s t) := by
  have hr := entryRadius_pos' s t
  have hr1 : (entryRadius (s, t) : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : entryRadius (s, t) + 1 ≠ 0)
  have hr2 := entryRadius_sq_complex s t
  have h1 : (1 + (s : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + s ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hw := one_sub_xi_sq_ne s t
  have hN := r1_sq_add_z_sq s t
  have hD : ((entryRadius (s, t) : ℂ) + 1) ^ 2 - ((t : ℂ) + I * s) ^ 2 =
      2 * (1 + (s : ℂ) ^ 2 + entryRadius (s, t) - t * s * I) := by
    linear_combination hr2 - ((s : ℂ) ^ 2) * Complex.I_sq
  have key : (-(s : ℂ) * t + I * entryRadius (s, t)) *
      (1 + (s : ℂ) ^ 2 + entryRadius (s, t) - t * s * I) =
      I * (1 + (s : ℂ) ^ 2) * (1 + (t : ℂ) ^ 2 + entryRadius (s, t) + t * s * I) := by
    linear_combination (-((s : ℂ) * t * entryRadius (s, t)) - s * t * (1 + (s : ℂ) ^ 2)) * Complex.I_sq +
      I * hr2
  have hz : ((entryRadius (s, t) : ℂ) + 1) ^ 2 - ((t : ℂ) + I * s) ^ 2 ≠ 0 := by
    have : 1 - xiOf s t ^ 2 = (((entryRadius (s, t) : ℂ) + 1) ^ 2 - ((t : ℂ) + I * s) ^ 2) /
        ((entryRadius (s, t) : ℂ) + 1) ^ 2 := by
      unfold xiOf; field_simp
    intro h0
    apply hw
    rw [this, h0, zero_div]
  have hD' : (1 + (s : ℂ) ^ 2 + entryRadius (s, t) - t * s * I) ≠ 0 := by
    intro h0
    apply hz
    rw [hD, h0, mul_zero]
  unfold entryTau tauOf xiOf
  have e1 : 1 + (((t : ℂ) + I * s) / ((entryRadius (s, t) : ℂ) + 1)) ^ 2 =
      (2 * (1 + (t : ℂ) ^ 2 + entryRadius (s, t) + t * s * I)) / ((entryRadius (s, t) : ℂ) + 1) ^ 2 := by
    rw [← hN]; field_simp
  have e2 : 1 - (((t : ℂ) + I * s) / ((entryRadius (s, t) : ℂ) + 1)) ^ 2 =
      (2 * (1 + (s : ℂ) ^ 2 + entryRadius (s, t) - t * s * I)) / ((entryRadius (s, t) : ℂ) + 1) ^ 2 := by
    rw [← hD]; field_simp
  rw [e1, e2]
  have hrhs : I * (2 * (1 + (t : ℂ) ^ 2 + entryRadius (s, t) + t * s * I) /
        ((entryRadius (s, t) : ℂ) + 1) ^ 2) /
      (2 * (1 + (s : ℂ) ^ 2 + entryRadius (s, t) - t * s * I) / ((entryRadius (s, t) : ℂ) + 1) ^ 2) =
      I * (1 + (t : ℂ) ^ 2 + entryRadius (s, t) + t * s * I) /
        (1 + (s : ℂ) ^ 2 + entryRadius (s, t) - t * s * I) := by
    field_simp
  rw [hrhs]
  push_cast
  rw [div_eq_div_iff h1 hD']
  linear_combination key


theorem coefA_mul (s t : ℝ) :
    entryCoefficientA (s, t) * (entryRadius (s, t) : ℂ) = -xiOf s t * (entryTau (s, t) + I) := by
  have hr := entryRadius_pos' s t
  have hrC : (entryRadius (s, t) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr1 : (entryRadius (s, t) : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : entryRadius (s, t) + 1 ≠ 0)
  have hr2 := entryRadius_sq_complex s t
  have h1 : (1 + (s : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + s ^ 2 := by positivity
    exact_mod_cast this.ne'
  have key : ((entryRadius (s, t) : ℂ) * s - I * t) * ((entryRadius (s, t) : ℂ) + 1) =
      -((t : ℂ) + I * s) * (-(s : ℂ) * t + I * entryRadius (s, t) + I + I * (s : ℂ) ^ 2) := by
    linear_combination (s : ℂ) * hr2 +
      ((s : ℂ) + s * (entryRadius (s, t) : ℂ) + (s : ℂ) ^ 3) * Complex.I_sq
  unfold entryCoefficientA xiOf entryTau
  push_cast
  field_simp
  linear_combination key


theorem coefB_mul (s t : ℝ) :
    entryCoefficient (s, t) * (entryRadius (s, t) : ℂ) =
      I / 2 * (1 + xiOf s t ^ 2) * (entryTau (s, t) + I) := by
  have hr := entryRadius_pos' s t
  have hrC : (entryRadius (s, t) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr1 : (entryRadius (s, t) : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : entryRadius (s, t) + 1 ≠ 0)
  have hr2 := entryRadius_sq_complex s t
  have h1 : (1 + (s : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + s ^ 2 := by positivity
    exact_mod_cast this.ne'
  have key : -((entryRadius (s, t) : ℂ) + s * t * I) * ((entryRadius (s, t) : ℂ) + 1) ^ 2 =
      I * (1 + (t : ℂ) ^ 2 + entryRadius (s, t) + t * s * I) *
        (-(s : ℂ) * t + I * entryRadius (s, t) + I + I * (s : ℂ) ^ 2) := by
    linear_combination
      (-2 - Complex.I ^ 2 - (entryRadius (s, t) : ℂ) - (s : ℂ) * t * I) * hr2 +
      (-2 - 2 * (entryRadius (s, t) : ℂ) - 2 * (t : ℂ) ^ 2 - (t : ℂ) ^ 2 * entryRadius (s, t) -
        (s : ℂ) * t * I - (s : ℂ) * t * (entryRadius (s, t) : ℂ) * I - 2 * (s : ℂ) ^ 2 -
        (s : ℂ) ^ 2 * entryRadius (s, t) - (s : ℂ) ^ 3 * t * I) * Complex.I_sq
  unfold entryCoefficient xiOf entryTau
  push_cast
  field_simp
  linear_combination 2 * key - I * (-(s : ℂ) * t + I * entryRadius (s, t) + I * (1 + (s : ℂ) ^ 2)) *
    r1_sq_add_z_sq s t


/-- The coefficient of the linear-form power `(a X₀ + b X₁ + c X₂)ⁿ`. -/
theorem coeff_linForm_pow (a b c : ℂ) (n : ℕ) (m : Fin 3 →₀ ℕ) :
    ((C a * X 0 + C b * X 1 + C c * X 2 : MvPolynomial (Fin 3) ℂ) ^ n).coeff m =
      if m.sum (fun _ k => k) = n then
        (m.multinomial : ℂ) * (a ^ (m 0) * b ^ (m 1) * c ^ (m 2)) else 0 := by
  have hform : (C a * X 0 + C b * X 1 + C c * X 2 : MvPolynomial (Fin 3) ℂ) =
      ∑ i : Fin 3, (![a, b, c] i) • (X i : MvPolynomial (Fin 3) ℂ) := by
    simp [Fin.sum_univ_three, smul_eq_C_mul]
  rw [hform, MvPolynomial.coeff_linearCombination_X_pow_of_fintype]
  split_ifs with hm
  · rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_three]
    simp
  · rfl


/-- The coefficient-dependent polynomial factor of the base-point integrand. -/
def xiPoly (m : Fin 3 →₀ ℕ) (ξ : ℂ) : ℂ :=
  (-2 * I * ξ) ^ (m 0) * (-(1 + ξ ^ 2)) ^ (m 1) * (I * (1 - ξ ^ 2)) ^ (m 2)

theorem tauOf_add_I (ξ : ℂ) (hw : 1 - ξ ^ 2 ≠ 0) : tauOf ξ + I = 2 * I / (1 - ξ ^ 2) := by
  unfold tauOf; field_simp; ring

theorem sum_eq_of_multinomial (m : Fin 3 →₀ ℕ) : m.sum (fun _ k => k) = m 0 + m 1 + m 2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three]

/-- **The coefficient of the seed's frame coefficient at `L_{s,t}` in the disc variable.** -/
theorem coeff_frameCoefficient_xi (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ)
    (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hst : (s, t) ≠ (0, 0)) :
    (frameCoefficient (seedForm n h) (entryFrame s t) V W).coeff m =
      ((m.multinomial : ℂ) * (I / 2) * ((2 * I) ^ (n + 3))⁻¹ * ((entryRadius (s, t) : ℂ) ^ (n + 3))⁻¹) *
        (entryDiscFn n h (xiOf s t ^ 2) *
          (xiPoly m (xiOf s t) * wedgePoly (V + V.transpose) (W + W.transpose) (xiOf s t))) := by
  have hr := entryRadius_pos' s t
  have hrC : (entryRadius (s, t) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hξ := xiOf_ne_zero s t hst
  have hw := one_sub_xi_sq_ne s t
  have hτ := tau_eq_tauOf s t
  have hwedge := wedgeSym_dirSymC_closed (entryRadius (s, t) : ℂ) (xiOf s t) hξ hw hrC
    (V + V.transpose) (W + W.transpose)
  rw [← s_eq_sOf s t hst, ← t_eq_tOf s t hst, ← tau_eq_tauOf s t] at hwedge
  rw [seed_frameCoefficient_entryFrame_sym, MvPolynomial.coeff_C_mul, coeff_linForm_pow, ite_eq_left hm]
  simp only [dirSym_eq_dirSymC]
  rw [hwedge]
  have ha := coefA_mul s t
  have hb := coefB_mul s t
  rw [hτ, tauOf_add_I _ hw] at ha
  rw [hτ, tauOf_add_I _ hw] at hb
  have ha' : entryCoefficientA (s, t) = -2 * I * xiOf s t / ((entryRadius (s, t) : ℂ) * (1 - xiOf s t ^ 2)) := by
    field_simp at ha ⊢
    linear_combination ha
  have hb' : entryCoefficient (s, t) = -(1 + xiOf s t ^ 2) / ((entryRadius (s, t) : ℂ) * (1 - xiOf s t ^ 2)) := by
    field_simp at hb ⊢
    linear_combination hb + (1 + xiOf s t ^ 2) * Complex.I_sq
  have hh : h (entryTau (s, t)) = entryDiscFn n h (xiOf s t ^ 2) / (2 * I / (1 - xiOf s t ^ 2)) ^ (n + 3) := by
    unfold entryDiscFn
    rw [hτ]
    have : (2 * I / (1 - xiOf s t ^ 2)) ^ (n + 3) ≠ 0 := by
      apply pow_ne_zero
      exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hw
    field_simp
    rfl
  have hn : n = m 0 + m 1 + m 2 := by rw [← hm, sum_eq_of_multinomial]
  rw [hh, ha', hb']
  unfold xiPoly
  subst hn
  have hu : (1 - xiOf s t ^ 2) ≠ 0 := hw
  have hI : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  simp only [div_pow, mul_pow, pow_add]
  field_simp

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
