module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Symmetric.ProjectionDerivBase

@[expose] public section


/-!
# Derivatives of the projection to the plane symmetric space at orthogonal matrices

Writing `S'(W) = W kᵀ + k Wᵀ` for the derivative of the Gram matrix at an orthogonal matrix `k`,
where the Gram matrix is the identity, the radical coordinate `S_{·2} / S₂₂` has derivative
`S'_{·2}` and the Levi point `(M₀₁ + i √det M) / M₁₁` has derivative `S'₀₁ + (i / 2) (S'₀₀ - S'₁₁)`:
at `S = 1` the Schur complement `M` has derivative `S'_{tl}`, `det M` has derivative
`S'₀₀ + S'₁₁`, and `√det M / M₁₁` has derivative `(S'₀₀ + S'₁₁) / 2 - S'₁₁`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

/-! ### Calculus at a point where the denominators are one -/

section Values

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

theorem hasFDerivAt_div_zero_one {c d : E → ℝ} {c' d' : E →L[ℝ] ℝ} (hc : HasFDerivAt c c' x)
    (hd : HasFDerivAt d d' x) (h0 : c x = 0) (h1 : d x = 1) :
    HasFDerivAt (fun y => c y / d y) c' x := by
  have product := hc.mul ((hasFDerivAt_inv (h1 ▸ one_ne_zero : d x ≠ 0)).comp x hd)
  have hfun : (fun y => c y / d y) = c * ((fun t : ℝ => t⁻¹) ∘ d) := by
    funext y
    simp [div_eq_mul_inv]
  rw [hfun]
  refine product.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [h0, h1]

theorem hasFDerivAt_schur_values {c p q d : E → ℝ} {c' p' q' d' : E →L[ℝ] ℝ}
    (hc : HasFDerivAt c c' x) (hp : HasFDerivAt p p' x) (hq : HasFDerivAt q q' x)
    (hd : HasFDerivAt d d' x) (hp0 : p x = 0) (hq0 : q x = 0) (h1 : d x = 1) :
    HasFDerivAt (fun y => c y - p y * q y / d y) c' x := by
  have quotient := hasFDerivAt_div_zero_one (hp.mul hq) hd (by simp [hp0]) h1
  refine (hc.sub quotient).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [hp0, hq0]

theorem hasFDerivAt_det_values {a b c e : E → ℝ} {a' b' c' e' : E →L[ℝ] ℝ}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) (hc : HasFDerivAt c c' x)
    (he : HasFDerivAt e e' x) (ha1 : a x = 1) (hb1 : b x = 1) (hc0 : c x = 0) (he0 : e x = 0) :
    HasFDerivAt (fun y => a y * b y - c y * e y) (a' + b') x := by
  refine ((ha.mul hb).sub (hc.mul he)).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [ha1, hb1, hc0, he0]
  ring

theorem hasFDerivAt_sqrt_div_values {D q : E → ℝ} {D' q' : E →L[ℝ] ℝ}
    (hD : HasFDerivAt D D' x) (hq : HasFDerivAt q q' x) (hD1 : D x = 1) (hq1 : q x = 1) :
    HasFDerivAt (fun y => Real.sqrt (D y) / q y) ((1 / 2 : ℝ) • D' - q') x := by
  have root := hD.sqrt (by rw [hD1]; exact one_ne_zero)
  have product := root.mul ((hasFDerivAt_inv (hq1 ▸ one_ne_zero : q x ≠ 0)).comp x hq)
  have hfun : (fun y => Real.sqrt (D y) / q y) =
      (fun y => Real.sqrt (D y)) * ((fun t : ℝ => t⁻¹) ∘ q) := by
    funext y
    simp [div_eq_mul_inv]
  rw [hfun]
  refine product.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [hD1, hq1]
  ring

theorem hasFDerivAt_complex_combination {f g : E → ℝ} {f' B C : E →L[ℝ] ℝ}
    {L : E →L[ℝ] ℂ} (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g ((1 / 2 : ℝ) • (B + C) - C) x)
    (hL : ∀ v, L v = (f' v : ℂ) + (Complex.I / 2) * ((B v : ℂ) - (C v : ℂ))) :
    HasFDerivAt (fun y => (f y : ℂ) + Complex.I * (g y : ℂ)) L x := by
  have total := (Complex.ofRealCLM.hasFDerivAt.comp x hf).add
    ((Complex.ofRealCLM.hasFDerivAt.comp x hg).const_mul Complex.I)
  refine total.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [hL]
  simp
  ring

end Values

/-! ### The derivatives -/

/-- **The derivative of the radical coordinate at an orthogonal matrix** is `W ↦ S'(W)_{·2}`. -/
theorem hasFDerivAt_symmetricRadical {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    HasFDerivAt symmetricRadical (radicalDeriv k) k := by
  have hS := gramMatrix_orthogonal hk
  refine hasFDerivAt_pi'.2 fun i => ?_
  have h0 : gramMatrix k i.castSucc 2 = 0 := by
    rw [hS]; fin_cases i <;> rfl
  have h1 : gramMatrix k 2 2 = 1 := by rw [hS]; rfl
  have quotient := hasFDerivAt_div_zero_one (hasFDerivAt_gramMatrix_apply k i.castSucc 2)
    (hasFDerivAt_gramMatrix_apply k 2 2) h0 h1
  exact quotient.congr_fderiv (ContinuousLinearMap.ext fun W => rfl)

theorem hasFDerivAt_symmetricSchur_apply {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1)
    (i j : Fin 2) :
    HasFDerivAt (fun z => symmetricSchur z i j) (gramEntryDeriv k i.castSucc j.castSucc) k := by
  have hS := gramMatrix_orthogonal hk
  have h0 : ∀ l : Fin 2, gramMatrix k l.castSucc 2 = 0 := by
    intro l; rw [hS]; fin_cases l <;> rfl
  have h1 : gramMatrix k 2 2 = 1 := by rw [hS]; rfl
  have g := hasFDerivAt_gramMatrix_apply k
  exact hasFDerivAt_schur_values (g _ _) (g _ _) (g _ _) (g 2 2) (h0 i) (h0 j) h1

/-- **The derivative of the Levi point at an orthogonal matrix** is
`W ↦ S'₀₁ + (i / 2) (S'₀₀ - S'₁₁)`. -/
theorem hasFDerivAt_symmetricPoint {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    HasFDerivAt symmetricPoint (pointDeriv k) k := by
  have hM := symmetricSchur_orthogonal hk
  have m := hasFDerivAt_symmetricSchur_apply hk
  have v00 : symmetricSchur k 0 0 = 1 := by rw [hM]; rfl
  have v11 : symmetricSchur k 1 1 = 1 := by rw [hM]; rfl
  have v01 : symmetricSchur k 0 1 = 0 := by rw [hM]; rfl
  have v10 : symmetricSchur k 1 0 = 0 := by rw [hM]; rfl
  have det : HasFDerivAt (fun z => (symmetricSchur z).det)
      (gramEntryDeriv k 0 0 + gramEntryDeriv k 1 1) k := by
    simp only [Matrix.det_fin_two]
    exact hasFDerivAt_det_values (m 0 0) (m 1 1) (m 0 1) (m 1 0) v00 v11 v01 v10
  have vdet : (symmetricSchur k).det = 1 := by rw [hM, Matrix.det_one]
  have re := hasFDerivAt_div_zero_one (m 0 1) (m 1 1) v01 v11
  have im := hasFDerivAt_sqrt_div_values det (m 1 1) vdet v11
  have e : symmetricPoint = fun z =>
      ((symmetricSchur z 0 1 / symmetricSchur z 1 1 : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (symmetricSchur z).det / symmetricSchur z 1 1 : ℝ) : ℂ) := by
    funext z
    exact positivePoint_eq_add _
  rw [e]
  exact hasFDerivAt_complex_combination re im fun W => rfl

end TernaryPeriodPolynomials.AnalyticClasses
