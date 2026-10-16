module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityChart
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityWedge
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Seed
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Coefficient

@[expose] public section


/-!
# The seed's frame coefficient at `L = w₀⁻¹u(s,t)` for arbitrary tangent directions

For a symmetric direction `p` (`p = V + Vᵀ`) the plane-chart tangent of the seed at the Gram matrix `L Lᵀ`,
`L = entryFrame s t`, is computed in closed form from `FormIdentityChart`:

* `β(dL p) = Ψ/R - ν D/R²`, `dτ(dL p) = (i r/2)(Π - 2νΨ/R + (1+τ²) D/R)` with `ν = s - τ t`, `R = r²`, where
  `(Ψ, Π, D) = dirSym p s t τ` are the symbols of `p` (`beta_entryFrame`, `dtau_entryFrame`);
* hence `(β ∧ dτ)(V, W) = wedgeSym r s t τ (dirSym (V+Vᵀ)) (dirSym (W+Wᵀ))` (`frame_wedge_entryFrame_sym`, using
  `ν² = R(1+τ²)`, from the quadratic equation of `τ = entryTau`);
* `seed_frameCoefficient_entryFrame_sym`: the frame coefficient of `seedForm n h` at `L` for arbitrary `V, W` is
  `h(τ) · wedgeSym · (aX + bY + (i/r)Z)ⁿ` (`seed_frameCoefficient_entryFrame` is the case
  `V = E₁₃, W = E₂₃`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open MvPolynomial
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryCoefficient

/-- The symbols `(Ψ, Π, D)` of a symmetric direction `p` at the base point `(s, t, τ)`. -/
def dirSym (p : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (τ : ℂ) : Symbols where
  psi := ((p 0 1 : ℂ) - τ * p 0 2) + ((p 1 1 : ℂ) * s + p 1 2 * t) - τ * ((p 1 2 : ℂ) * s + p 2 2 * t)
  pi := (p 1 1 : ℂ) - 2 * τ * p 1 2 + τ ^ 2 * p 2 2
  d := (p 0 0 : ℂ) + 2 * ((p 0 1 : ℂ) * s + p 0 2 * t) + p 1 1 * s ^ 2 + 2 * p 1 2 * s * t + p 2 2 * t ^ 2

theorem entryFrame_gram_eq (s t : ℝ) : entryFrame s t * (entryFrame s t).transpose =
    !![1, 0, s; 0, 1, t; s, t, 1 + s ^ 2 + t ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [entryFrame, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  all_goals ring

theorem entryFrame_dir_eq (s t : ℝ) (p : Matrix (Fin 3) (Fin 3) ℝ) (hp : p.IsSymm) :
    entryFrame s t * p * (entryFrame s t).transpose =
      !![p 1 1, p 1 2, p 0 1 + s * p 1 1 + t * p 1 2;
         p 1 2, p 2 2, p 0 2 + s * p 1 2 + t * p 2 2;
         p 0 1 + s * p 1 1 + t * p 1 2, p 0 2 + s * p 1 2 + t * p 2 2,
         p 0 0 + 2 * (p 0 1 * s + p 0 2 * t) + p 1 1 * s ^ 2 + 2 * p 1 2 * s * t + p 2 2 * t ^ 2] := by
  have h10 : p 1 0 = p 0 1 := hp.apply 0 1
  have h20 : p 2 0 = p 0 2 := hp.apply 0 2
  have h21 : p 2 1 = p 1 2 := hp.apply 1 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [entryFrame, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul, dotProduct, h10, h20, h21] <;> ring


theorem entryCurve_zero_eq (s t : ℝ) : entryCurve s t 0 0 = entryFrame s t * (entryFrame s t).transpose := by
  simp [entryCurve]

theorem gramPlaneTau_entryFrame (s t : ℝ) :
    gramPlaneTau (entryFrame s t * (entryFrame s t).transpose) = entryTau (s, t) := by
  rw [← entryCurve_zero_eq]; exact (real_entry_tangent s t).2.1

theorem entryTau_quadratic (s t : ℝ) :
    (1 + (s : ℂ) ^ 2) * entryTau (s, t) ^ 2 + 2 * s * t * entryTau (s, t) + 1 + (t : ℂ) ^ 2 = 0 := by
  have hr2 : (entryRadius (s, t) : ℂ) ^ 2 = 1 + (s : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + s ^ 2 + t ^ 2 by positivity)
    unfold entryRadius
    exact_mod_cast this
  have hs : (1 + (s : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + s ^ 2 := by positivity
    exact_mod_cast this.ne'
  unfold entryTau
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * hr2 + (entryRadius (s, t) : ℂ) ^ 2 * Complex.I_sq


theorem entryRadius_sq_complex (s t : ℝ) :
    (entryRadius (s, t) : ℂ) ^ 2 = 1 + (s : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + s ^ 2 + t ^ 2 by positivity)
  unfold entryRadius
  exact_mod_cast this

/-- `β` of a symmetric direction at the base point:
`β(dL_L p) = Ψ/R - ν D/R²`, `ν = s - τ t`, `R = r²`. -/
theorem beta_entryFrame (s t : ℝ) (p : Matrix (Fin 3) (Fin 3) ℝ) (hp : p.IsSymm) :
    (planeDU (entryFrame s t * (entryFrame s t).transpose)
        (entryFrame s t * p * (entryFrame s t).transpose) 0 : ℂ) -
      entryTau (s, t) * (planeDU (entryFrame s t * (entryFrame s t).transpose)
        (entryFrame s t * p * (entryFrame s t).transpose) 1 : ℂ) =
    (dirSym p s t (entryTau (s, t))).psi / (entryRadius (s, t) : ℂ) ^ 2 -
      ((s : ℂ) - entryTau (s, t) * t) * (dirSym p s t (entryTau (s, t))).d /
        (entryRadius (s, t) : ℂ) ^ 4 := by
  have hr2 := entryRadius_sq_complex s t
  have hr : (entryRadius (s, t) : ℂ) ^ 2 ≠ 0 := by
    rw [hr2]
    have : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 := by positivity
    exact_mod_cast this.ne'
  rw [entryFrame_gram_eq, entryFrame_dir_eq s t p hp]
  simp only [planeDU, dirSym]
  simp
  rw [show (entryRadius (s, t) : ℂ) ^ 4 = ((entryRadius (s, t) : ℂ) ^ 2) ^ 2 by ring, hr2] at *
  field_simp
  ring


theorem entryFrame_det_eq (s t : ℝ) : (entryFrame s t).det = 1 := by
  simp [entryFrame, Matrix.det_fin_three]

theorem entryFrame_gram_isSymm (s t : ℝ) : (entryFrame s t * (entryFrame s t).transpose).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gramSchur_det_entryFrame (s t : ℝ) :
    (gramSchur (entryFrame s t * (entryFrame s t).transpose)).det = 1 / (1 + s ^ 2 + t ^ 2) := by
  have hR : (entryFrame s t * (entryFrame s t).transpose) 2 2 = 1 + s ^ 2 + t ^ 2 := by
    rw [entryFrame_gram_eq]; simp
  rw [gramSchur_det_eq' _ (entryFrame_gram_isSymm s t) (by rw [hR]; positivity), hR, Matrix.det_mul,
    Matrix.det_transpose, entryFrame_det_eq]
  simp

/-- `dτ` of a symmetric direction at the base point:
`dτ(dL_L p) = (i r/2)(Π - 2νΨ/R + (1+τ²) D/R)`. -/
theorem dtau_entryFrame (s t : ℝ) (p : Matrix (Fin 3) (Fin 3) ℝ) (hp : p.IsSymm) :
    planeDTau (entryFrame s t * (entryFrame s t).transpose)
        (entryFrame s t * p * (entryFrame s t).transpose) =
      Complex.I * (entryRadius (s, t) : ℂ) / 2 *
        ((dirSym p s t (entryTau (s, t))).pi -
          2 * ((s : ℂ) - entryTau (s, t) * t) * (dirSym p s t (entryTau (s, t))).psi /
            (entryRadius (s, t) : ℂ) ^ 2 +
          (1 + entryTau (s, t) ^ 2) * (dirSym p s t (entryTau (s, t))).d / (entryRadius (s, t) : ℂ) ^ 2) := by
  have hr2 := entryRadius_sq_complex s t
  have hrpos : 0 < entryRadius (s, t) := Real.sqrt_pos.mpr (by positivity)
  have hr : (entryRadius (s, t) : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hQ := entryTau_quadratic s t
  have hν : ((s : ℂ) - entryTau (s, t) * t) ^ 2 =
      (entryRadius (s, t) : ℂ) ^ 2 * (1 + entryTau (s, t) ^ 2) := by
    rw [hr2]; linear_combination (-1 : ℂ) * hQ
  have hsq : Real.sqrt (1 / (1 + s ^ 2 + t ^ 2)) = 1 / entryRadius (s, t) := by
    unfold entryRadius
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one]
  unfold planeDTau
  rw [gramSchur_det_entryFrame, hsq, gramPlaneTau_entryFrame, entryFrame_gram_eq,
    entryFrame_dir_eq s t p hp]
  simp only [schurDeriv2, schurDeriv, dirSym]
  simp
  have hR : (1 + (s : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
    rw [← hr2]; exact pow_ne_zero 2 hr
  have hdist' : ∀ x : ℂ, (1 + entryTau (s, t) ^ 2) * x / (entryRadius (s, t) : ℂ) ^ 2 =
      ((s : ℂ) - entryTau (s, t) * t) ^ 2 * x / (1 + (s : ℂ) ^ 2 + (t : ℂ) ^ 2) ^ 2 := by
    intro x
    rw [hν, hr2]
    field_simp
  rw [hdist', hr2]
  field_simp
  ring


/-- The wedge of two directions computed from the tangent formulas (uses `ν² = R(1+τ²)`). -/
theorem wedge_of_tangents (r s t τ : ℂ) (hr : r ≠ 0) (hν : (s - τ * t) ^ 2 = r ^ 2 * (1 + τ ^ 2))
    (a b : Symbols) :
    (a.psi / r ^ 2 - (s - τ * t) * a.d / r ^ 4) *
        (Complex.I * r / 2 * (b.pi - 2 * (s - τ * t) * b.psi / r ^ 2 + (1 + τ ^ 2) * b.d / r ^ 2)) -
      (b.psi / r ^ 2 - (s - τ * t) * b.d / r ^ 4) *
        (Complex.I * r / 2 * (a.pi - 2 * (s - τ * t) * a.psi / r ^ 2 + (1 + τ ^ 2) * a.d / r ^ 2)) =
      wedgeSym r s t τ a b := by
  unfold wedgeSym
  field_simp
  linear_combination (-2 * (a.psi * b.d - a.d * b.psi)) * hν


/-- `β` of a direction `V` in the frame of `L` is the `β`-tangent of `p = V + Vᵀ`. -/
theorem frameBeta_entryFrame_eq (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    frameBeta (entryFrame s t) V =
      (planeDU (entryFrame s t * (entryFrame s t).transpose)
          (entryFrame s t * (V + V.transpose) * (entryFrame s t).transpose) 0 : ℂ) -
        entryTau (s, t) * (planeDU (entryFrame s t * (entryFrame s t).transpose)
          (entryFrame s t * (V + V.transpose) * (entryFrame s t).transpose) 1 : ℂ) := by
  have hdet : (entryFrame s t).det ≠ 0 := by rw [entryFrame_det_eq]; exact one_ne_zero
  unfold frameBeta
  rw [chartTangent_eq _ _ hdet, ← gramPlaneTau_entryFrame]
  unfold planeTangent
  simp

theorem frameDTau_entryFrame_eq (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    frameDTau (entryFrame s t) V =
      planeDTau (entryFrame s t * (entryFrame s t).transpose)
          (entryFrame s t * (V + V.transpose) * (entryFrame s t).transpose) := by
  have hdet : (entryFrame s t).det ≠ 0 := by rw [entryFrame_det_eq]; exact one_ne_zero
  unfold frameDTau
  rw [chartTangent_eq _ _ hdet]
  unfold planeTangent
  simp
  rw [mul_comm]
  exact Complex.re_add_im _

theorem seedTau_gramChart_eq (G : Matrix (Fin 3) (Fin 3) ℝ) : seedTau (gramChart G) = gramPlaneTau G := by
  simp only [seedTau, gramChart, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_cons]
  rw [mul_comm]
  exact Complex.re_add_im _

/-- **The seed's frame coefficient at `L` for arbitrary tangent directions.** -/
theorem seed_frameCoefficient_entryFrame_gen (n : ℕ) (h : ℂ → ℂ) (s t : ℝ)
    (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    frameCoefficient (seedForm n h) (entryFrame s t) V W =
      C (h (entryTau (s, t)) *
          (frameBeta (entryFrame s t) V * frameDTau (entryFrame s t) W -
            frameBeta (entryFrame s t) W * frameDTau (entryFrame s t) V)) *
        (C (entryCoefficientA (s, t)) * X 0 + C (entryCoefficient (s, t)) * X 1 +
          C (Complex.I / (entryRadius (s, t) : ℂ)) * X 2) ^ n := by
  obtain ⟨hU, hT, -⟩ := real_entry_tangent s t
  have hG : entryFrame s t * (entryFrame s t).transpose = entryCurve s t 0 0 := (entryCurve_zero_eq s t).symm
  have hlin := rho_entryFrame_inv_seedLinear s t (gramChart (entryFrame s t * (entryFrame s t).transpose))
    (by rw [hG]; rfl) (by rw [seedTau_gramChart_eq, hG])
  rw [rho_entryFrame_inv] at hlin
  rw [frameCoefficient, frameValue_seedForm, rho_entryFrame_inv, map_mul, map_pow,
    bind₁_C_right, hlin, gramPlaneTau_entryFrame]


/-- The wedge of the frame tangents of two directions at `L` is `wedgeSym` of their symbols. -/
theorem frame_wedge_entryFrame_sym (s t : ℝ) (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    frameBeta (entryFrame s t) V * frameDTau (entryFrame s t) W -
        frameBeta (entryFrame s t) W * frameDTau (entryFrame s t) V =
      wedgeSym (entryRadius (s, t) : ℂ) s t (entryTau (s, t))
        (dirSym (V + V.transpose) s t (entryTau (s, t)))
        (dirSym (W + W.transpose) s t (entryTau (s, t))) := by
  have hr2 := entryRadius_sq_complex s t
  have hrpos : 0 < entryRadius (s, t) := Real.sqrt_pos.mpr (by positivity)
  have hr : (entryRadius (s, t) : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hQ := entryTau_quadratic s t
  have hν : ((s : ℂ) - entryTau (s, t) * t) ^ 2 =
      (entryRadius (s, t) : ℂ) ^ 2 * (1 + entryTau (s, t) ^ 2) := by
    rw [hr2]; linear_combination (-1 : ℂ) * hQ
  have hsV : (V + V.transpose).IsSymm := Matrix.isSymm_add_transpose_self V
  have hsW : (W + W.transpose).IsSymm := Matrix.isSymm_add_transpose_self W
  rw [frameBeta_entryFrame_eq, frameBeta_entryFrame_eq, frameDTau_entryFrame_eq,
    frameDTau_entryFrame_eq, beta_entryFrame s t _ hsV, beta_entryFrame s t _ hsW,
    dtau_entryFrame s t _ hsV, dtau_entryFrame s t _ hsW]
  exact wedge_of_tangents (entryRadius (s, t) : ℂ) s t (entryTau (s, t)) hr hν _ _

/-- **The seed's frame coefficient at `L` in terms of the symbols.** -/
theorem seed_frameCoefficient_entryFrame_sym (n : ℕ) (h : ℂ → ℂ) (s t : ℝ)
    (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    frameCoefficient (seedForm n h) (entryFrame s t) V W =
      C (h (entryTau (s, t)) *
          wedgeSym (entryRadius (s, t) : ℂ) s t (entryTau (s, t))
            (dirSym (V + V.transpose) s t (entryTau (s, t)))
            (dirSym (W + W.transpose) s t (entryTau (s, t)))) *
        (C (entryCoefficientA (s, t)) * X 0 + C (entryCoefficient (s, t)) * X 1 +
          C (Complex.I / (entryRadius (s, t) : ℂ)) * X 2) ^ n := by
  rw [seed_frameCoefficient_entryFrame_gen, frame_wedge_entryFrame_sym]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
