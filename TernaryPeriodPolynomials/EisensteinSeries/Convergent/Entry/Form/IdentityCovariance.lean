module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityLevi

@[expose] public section


/-!
# R2: covariance of the integrated frame coefficient under the line parabolic

`intFrameCoeff n h g V W m = ∫_{ℝ²} coeff_m ω̃_h(L_{s,t} g)(V,W) ds dt`.
* `intFrameCoeff_radicalTranslate` (R2a): invariance under left translation by the line radical `u(a,b)`
  (`L_{s,t} u(a,b) = L_{s+a,t+b}` and translation invariance of Lebesgue measure);
* `intFrameCoeff_lineParabolic` (R2b): for `q = [[a, bᵀ], [0, C]]` (`a > 0`, `det C > 0`),
  `intFrameCoeff n h (q g) = (a²/det C) · intFrameCoeff n h' g` with `h' = slashTwisted (n+3) C h`:
  `L_{s,t} q = diag(C, a) L_{s',t'}` with `(s',t')` an affine function of `(s,t)` of Jacobian `det C/a²`,
  the Levi covariance `frameCoefficient_planeLevi` (R1) and the change of variables
  `integral_comp_affine_prod`; `integrable_lineParabolic`: integrability is preserved by the same change of variables.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open MeasureTheory MvPolynomial TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

/-- **Change of variables under a linear automorphism of `ℝ²`**. -/
theorem integral_comp_linearMap_prod (f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (hf : LinearMap.det f ≠ 0)
    (g : ℝ × ℝ → ℂ) :
    ∫ v, g (f v) = (|LinearMap.det f|⁻¹ : ℝ) • ∫ v, g v := by
  let e := LinearMap.equivOfDetNeZero f hf
  have hme : MeasurableEmbedding f :=
    (e.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  rw [← hme.integral_map g, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hf,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rw [abs_inv]


/-- Change of variables under an affine automorphism of `ℝ²`. -/
theorem integral_comp_affine_prod (f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (hf : LinearMap.det f ≠ 0) (c : ℝ × ℝ)
    (g : ℝ × ℝ → ℂ) : ∫ v, g (f v + c) = (|LinearMap.det f|⁻¹ : ℝ) • ∫ v, g v := by
  let e := LinearMap.equivOfDetNeZero f hf
  have hfe : f (e.symm c) = c := e.apply_symm_apply c
  have h1 : ∫ v, g (f v + c) = ∫ v, g (f v) := by
    have := integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun v => g (f v + c)) (-(e.symm c))
    rw [← this]
    congr 1
    ext v
    simp [map_add, map_neg, hfe]
  rw [h1, integral_comp_linearMap_prod f hf]

/-- The linear part `(s,t) ↦ ((C₀₀ s + C₁₀ t)/a, (C₀₁ s + C₁₁ t)/a)` of the change of variables in R2b. -/
def affM (a : ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![C 0 0 / a, C 1 0 / a; C 0 1 / a, C 1 1 / a]

theorem affM_apply (a : ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) (s t : ℝ) :
    affM a C (s, t) = ((C 0 0 * s + C 1 0 * t) / a, (C 0 1 * s + C 1 1 * t) / a) := by
  unfold affM
  rw [Matrix.toLin_apply]
  simp [Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Fin.sum_univ_two]
  constructor <;> ring

theorem affM_det (a : ℝ) (ha : a ≠ 0) (C : Matrix (Fin 2) (Fin 2) ℝ) :
    LinearMap.det (affM a C) = C.det / a ^ 2 := by
  unfold affM
  rw [LinearMap.det_toLin, Matrix.det_fin_two, Matrix.det_fin_two]
  simp
  field_simp


/-- The integrated plane-seed frame coefficient (one polynomial coefficient `m`). -/
def intFrameCoeff (n : ℕ) (h : ℂ → ℂ) (g V W : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 →₀ ℕ) : ℂ :=
  ∫ st : ℝ × ℝ, (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) V W).coeff m

/-- **R2a: `N_Q`-invariance.** -/
theorem intFrameCoeff_radicalTranslate (n : ℕ) (h : ℂ → ℂ) (a b : ℝ) (g V W : Matrix (Fin 3) (Fin 3) ℝ)
    (m : Fin 3 →₀ ℕ) :
    intFrameCoeff n h (radicalTranslate a b * g) V W m = intFrameCoeff n h g V W m := by
  unfold intFrameCoeff
  have hmat : ∀ st : ℝ × ℝ, entryFrame st.1 st.2 * (radicalTranslate a b * g) =
      entryFrame (st.1 + a) (st.2 + b) * g := by
    intro st; rw [← Matrix.mul_assoc, entryFrame_mul_radicalTranslate]
  simp_rw [hmat]
  exact integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
    (fun st : ℝ × ℝ => (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * g) V W).coeff m) (a, b)

/-- The pointwise identity behind R2b: the integrand for `q g` is the integrand for `slashTwisted C h` and `g`
evaluated at an affine function of `(s,t)`. -/
theorem integrand_lineParabolic (n : ℕ) (h : ℂ → ℂ) (a : ℝ) (b : Fin 2 → ℝ)
    (C : Matrix (Fin 2) (Fin 2) ℝ) (ha : 0 < a) (hC : 0 < C.det) (g V W : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : g.det ≠ 0) (m : Fin 3 →₀ ℕ) (st : ℝ × ℝ) :
    (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * (lineParabolic a b C * g)) V W).coeff m =
      (frameCoefficient (seedForm n (slashTwisted (n + 3) C h))
          (entryFrame (affM a C st + (b 0 / a, b 1 / a)).1 (affM a C st + (b 0 / a, b 1 / a)).2 * g) V W).coeff m := by
  obtain ⟨s, t⟩ := st
  rw [affM_apply]
  have h1 : entryFrame s t * (lineParabolic a b C * g) =
      planeLevi C a * (entryFrame ((b 0 + C 0 0 * s + C 1 0 * t) / a) ((b 1 + C 0 1 * s + C 1 1 * t) / a) * g) := by
    rw [← Matrix.mul_assoc, entryFrame_mul_lineParabolic s t a b C ha.ne', Matrix.mul_assoc]
  have hdet : (entryFrame ((b 0 + C 0 0 * s + C 1 0 * t) / a) ((b 1 + C 0 1 * s + C 1 1 * t) / a) * g).det ≠ 0 := by
    rw [Matrix.det_mul, entryFrame_det_eq, one_mul]; exact hg
  rw [h1, frameCoefficient_planeLevi n h C a hC ha _ V W hdet]
  simp only [Prod.mk_add_mk]
  congr 3
  field_simp
  ring_nf

/-- **R2b: `M_Q`-covariance.** -/
theorem intFrameCoeff_lineParabolic (n : ℕ) (h : ℂ → ℂ) (a : ℝ) (b : Fin 2 → ℝ)
    (C : Matrix (Fin 2) (Fin 2) ℝ) (ha : 0 < a) (hC : 0 < C.det) (g V W : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : g.det ≠ 0) (m : Fin 3 →₀ ℕ) :
    intFrameCoeff n h (lineParabolic a b C * g) V W m =
      ((a ^ 2 / C.det : ℝ) : ℂ) * intFrameCoeff n (slashTwisted (n + 3) C h) g V W m := by
  unfold intFrameCoeff
  set F : ℝ × ℝ → ℂ := fun st => (frameCoefficient (seedForm n (slashTwisted (n + 3) C h)) (entryFrame st.1 st.2 * g) V W).coeff m with hF
  have hmat : ∀ st : ℝ × ℝ, (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * (lineParabolic a b C * g)) V W).coeff m =
      F (affM a C st + (b 0 / a, b 1 / a)) := fun st => integrand_lineParabolic n h a b C ha hC g V W hg m st
  simp_rw [hmat]
  have hdet2 : LinearMap.det (affM a C) ≠ 0 := by
    rw [affM_det a ha.ne']; positivity
  rw [integral_comp_affine_prod (affM a C) hdet2 (b 0 / a, b 1 / a) F, affM_det a ha.ne']
  rw [Complex.real_smul]
  congr 1
  push_cast
  rw [abs_of_pos (by positivity)]
  have hCne : (C.det : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [Complex.ofReal_div, Complex.ofReal_pow]
  field_simp

/-- Integrability transfers under the change of variables of R2b. -/
theorem integrable_lineParabolic (n : ℕ) (h : ℂ → ℂ) (a : ℝ) (b : Fin 2 → ℝ)
    (C : Matrix (Fin 2) (Fin 2) ℝ) (ha : 0 < a) (hC : 0 < C.det) (g V W : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : g.det ≠ 0) (m : Fin 3 →₀ ℕ)
    (hint : Integrable (fun st : ℝ × ℝ => (frameCoefficient (seedForm n (slashTwisted (n + 3) C h)) (entryFrame st.1 st.2 * g) V W).coeff m)) :
    Integrable (fun st : ℝ × ℝ => (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * (lineParabolic a b C * g)) V W).coeff m) := by
  set F : ℝ × ℝ → ℂ := fun st => (frameCoefficient (seedForm n (slashTwisted (n + 3) C h)) (entryFrame st.1 st.2 * g) V W).coeff m with hF
  have hmat : (fun st : ℝ × ℝ => (frameCoefficient (seedForm n h) (entryFrame st.1 st.2 * (lineParabolic a b C * g)) V W).coeff m) =
      fun st => F (affM a C st + (b 0 / a, b 1 / a)) :=
    funext fun st => integrand_lineParabolic n h a b C ha hC g V W hg m st
  rw [hmat]
  have hdet2 : LinearMap.det (affM a C) ≠ 0 := by
    rw [affM_det a ha.ne']; positivity
  let e := LinearMap.equivOfDetNeZero (affM a C) hdet2
  have hme : MeasurableEmbedding (affM a C) :=
    (e.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have h1 : Integrable (fun v : ℝ × ℝ => F (v + (b 0 / a, b 1 / a))) := hint.comp_add_right _
  have h2 : Integrable (fun v : ℝ × ℝ => F (v + (b 0 / a, b 1 / a)))
      (Measure.map (affM a C) volume) := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet2]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  exact (hme.integrable_map_iff).mp h2

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
