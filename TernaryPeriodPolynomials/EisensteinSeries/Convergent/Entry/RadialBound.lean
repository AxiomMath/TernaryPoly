module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityBase
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityCovariance
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityAssembly

@[expose] public section


/-!
# `L¹` bounds for the seed along a line-parabolic frame

`radial_bound_explicit`: the radial decay `‖coeff_m ω̃_h(L_{s,t})(V,W)‖ ≤ √A r⁻³` with an explicit constant `A`
(`radialA`) in terms of the decay constant `M` of `h` and a bound `C` of the wedge polynomial.  Transported by the
change of variables of `R2` (`integrand_lineParabolic`), `l1_bound_lineParabolic` bounds
`∫ ‖coeff_ν ω̃_h(L_u q)(V,W)‖ du` for `q = [[a, bᵀ],[0, C]]` by `(a²/det C) √A' K₃`, `K₃ = ∫ r⁻³`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The explicit constant of the radial bound. -/
def radialA (n : ℕ) (M : ℝ) (m : Fin 3 →₀ ℕ) (C : ℝ) : ℝ :=
  ((m.multinomial : ℝ) / 2 ^ (n + 4)) ^ 2 * M * 4 ^ (n + 3) * (2 ^ (m 0 + m 1 + m 2)) ^ 2 * C ^ 2

/-- **The radial decay with explicit constant**: `‖coeff_m ω̃_h(L_{s,t})(V,W)‖ ≤ √A · r⁻³` with
`A = radialA n M m C`, for any bound `C` of the wedge polynomial on the closed unit disc. -/
theorem radial_bound_explicit (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : ContinuousOn h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (m : Fin 3 →₀ ℕ)
    (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ)
    (hC : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖wedgePoly (V + V.transpose) (W + W.transpose) ξ‖ ≤ C) (st : ℝ × ℝ) :
    ‖(frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m‖ ≤
      Real.sqrt (radialA n M m C) * (entryRadius st)⁻¹ ^ 3 := by
  set A : ℝ := radialA n M m C with hA
  have hM0 : 0 ≤ M := by
    have := hM Complex.I (by simp)
    simp at this
    nlinarith [sq_nonneg ‖h Complex.I‖]
  have hA0 : 0 ≤ A := by unfold radialA at hA; rw [hA]; positivity
  have hcont := continuous_coeff_frameCoefficient n h hh m V W
  have hclosed : IsClosed {st : ℝ × ℝ |
      ‖(frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m‖ ≤
        Real.sqrt A * (entryRadius st)⁻¹ ^ 3} := by
    refine isClosed_le ?_ ?_
    · exact hcont.norm
    · exact continuous_const.mul ((entryRadius_continuous.inv₀ (fun st => (entryRadius_pos' st.1 st.2).ne')).pow 3)
  have hsub : {st : ℝ × ℝ | st ≠ (0, 0)} ⊆ {st : ℝ × ℝ |
      ‖(frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m‖ ≤
        Real.sqrt A * (entryRadius st)⁻¹ ^ 3} := by
    intro st hst
    obtain ⟨s, t⟩ := st
    have hsq := coeff_norm_sq_le n h M hM m hm V W C hC s t hst
    have hr := entryRadius_pos' s t
    have hr1 := entryRadius_ge_one' s t
    have h6 : (entryRadius (s, t) ^ 6)⁻¹ ≥ ((entryRadius (s, t)) ^ (n + 3))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ hr1 (by omega)
    have hle : ‖(frameCoefficient (seedForm n h) (entryFrame s t) V W).coeff m‖ ^ 2 ≤
        (Real.sqrt A * (entryRadius (s, t))⁻¹ ^ 3) ^ 2 := by
      calc _ ≤ A * ((entryRadius (s, t)) ^ (n + 3))⁻¹ := hsq
        _ ≤ A * (entryRadius (s, t) ^ 6)⁻¹ := by gcongr
        _ = (Real.sqrt A * (entryRadius (s, t))⁻¹ ^ 3) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hA0, ← pow_mul, inv_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle
  have hdense : Dense {st : ℝ × ℝ | st ≠ (0, 0)} := dense_compl_singleton ((0 : ℝ), (0 : ℝ))
  have := hclosed.closure_subset_iff.mpr hsub
  rw [hdense.closure_eq] at this
  exact this (Set.mem_univ st)

/-- The integral of the radial dominant. -/
def radK3 : ℝ := ∫ x : ℝ × ℝ, (entryRadius x)⁻¹ ^ 3

theorem integrable_radial_cube : Integrable (fun x : ℝ × ℝ => (entryRadius x)⁻¹ ^ 3) := by
  have hc : Continuous (fun x : ℝ × ℝ => (((entryRadius x)⁻¹ ^ 3 : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact (entryRadius_continuous.inv₀ (fun st => (entryRadius_pos' st.1 st.2).ne')).pow 3
  have := integrable_of_radial_bound _ hc 1 (fun st => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by have := entryRadius_pos' st.1 st.2; positivity)]
    simp)
  refine (this.norm).congr (Filter.Eventually.of_forall fun x => ?_)
  have hr := entryRadius_pos' x.1 x.2
  simp only [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (entryRadius x)⁻¹ ^ 3)]

theorem integral_comp_affine_real (f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (hf : LinearMap.det f ≠ 0) (c : ℝ × ℝ)
    (g : ℝ × ℝ → ℝ) : ∫ v, g (f v + c) = |LinearMap.det f|⁻¹ * ∫ v, g v := by
  have := integral_comp_affine_prod f hf c (fun v => (g v : ℂ))
  have h1 : ∫ v, ((g (f v + c) : ℝ) : ℂ) = ((∫ v, g (f v + c) : ℝ) : ℂ) := integral_complex_ofReal
  have h2 : ∫ v, ((g v : ℝ) : ℂ) = ((∫ v, g v : ℝ) : ℂ) := integral_complex_ofReal
  rw [h1, h2, Complex.real_smul] at this
  exact_mod_cast this

theorem integrable_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (hf : LinearMap.det f ≠ 0) (c : ℝ × ℝ) (g : ℝ × ℝ → E)
    (hg : Integrable g) : Integrable (fun v => g (f v + c)) := by
  let e := LinearMap.equivOfDetNeZero f hf
  have hme : MeasurableEmbedding f := (e.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have h1 : Integrable (fun v : ℝ × ℝ => g (v + c)) := hg.comp_add_right _
  have h2 : Integrable (fun v : ℝ × ℝ => g (v + c)) (Measure.map f volume) := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hf]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  exact (hme.integrable_map_iff).mp h2

/-- **The `L¹` bound of a coefficient of the seed frame coefficient at a line-parabolic frame**:
`∫_u ‖coeff_ν ω̃_h(L_u q)(V,W)‖ ≤ (a²/det C) · √(radialA …) · K₃`, `q = [[a, bᵀ],[0, C]]`. -/
theorem l1_bound_lineParabolic (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (a : ℝ) (b : Fin 2 → ℝ)
    (C : Matrix (Fin 2) (Fin 2) ℝ) (ha : 0 < a) (hC : 0 < C.det) (V W : Matrix (Fin 3) (Fin 3) ℝ)
    (Cw : ℝ) (hCw : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖wedgePoly (V + V.transpose) (W + W.transpose) ξ‖ ≤ Cw)
    (ν : Fin 3 →₀ ℕ) (hν : ν.sum (fun _ k => k) = n) :
    ∫ u : ℝ × ℝ, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * lineParabolic a b C) V W).coeff ν‖ ≤
      (a ^ 2 / C.det) * (Real.sqrt (radialA n (C.det ^ (n + 3) * M) ν Cw) * radK3) := by
  set h' := slashTwisted (n + 3) C h with hh'
  have hh' : DifferentiableOn ℂ h' {z : ℂ | 0 < z.im} := slashTwisted_differentiableOn (n + 3) C hC h hh
  have hM' : ∀ z : ℂ, 0 < z.im → ‖h' z‖ ^ 2 * z.im ^ (n + 3) ≤ C.det ^ (n + 3) * M :=
    fun z hz => slashTwisted_decay (n + 3) C hC h M hM z hz
  set D := Real.sqrt (radialA n (C.det ^ (n + 3) * M) ν Cw) with hD
  have hpt : ∀ u : ℝ × ℝ, (frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * lineParabolic a b C) V W).coeff ν =
      (frameCoefficient (seedForm n h')
        (entryFrame (affM a C u + (b 0 / a, b 1 / a)).1 (affM a C u + (b 0 / a, b 1 / a)).2) V W).coeff ν := by
    intro u
    have := integrand_lineParabolic n h a b C ha hC 1 V W (by simp) ν u
    simpa [Matrix.mul_one] using this
  set G : ℝ × ℝ → ℝ := fun x => D * (entryRadius x)⁻¹ ^ 3 with hG
  have hdet : LinearMap.det (affM a C) ≠ 0 := by
    rw [affM_det a ha.ne']; positivity
  have hGint : Integrable G := integrable_radial_cube.const_mul D
  have hGaff : Integrable (fun u => G (affM a C u + (b 0 / a, b 1 / a))) :=
    integrable_comp_affine _ hdet _ _ hGint
  have hle : ∀ u : ℝ × ℝ, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * lineParabolic a b C) V W).coeff ν‖ ≤
      G (affM a C u + (b 0 / a, b 1 / a)) := by
    intro u
    rw [hpt u]
    exact radial_bound_explicit n hn h' hh'.continuousOn _ hM' ν hν V W Cw hCw _
  calc ∫ u : ℝ × ℝ, ‖(frameCoefficient (seedForm n h) (entryFrame u.1 u.2 * lineParabolic a b C) V W).coeff ν‖
      ≤ ∫ u : ℝ × ℝ, G (affM a C u + (b 0 / a, b 1 / a)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) hGaff
          (Filter.Eventually.of_forall hle)
    _ = |LinearMap.det (affM a C)|⁻¹ * ∫ x, G x := integral_comp_affine_real _ hdet _ G
    _ = (a ^ 2 / C.det) * (D * radK3) := by
        rw [affM_det a ha.ne', abs_of_pos (by positivity), hG, integral_const_mul, radK3]
        field_simp

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem continuous_wedgePoly :
    Continuous (fun x : Mat3 × Mat3 × ℂ => wedgePoly x.1 x.2.1 x.2.2) := by
  unfold wedgePoly dirW dirCoef
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  have e : ∀ i j : Fin 3, Continuous (fun x : Mat3 × Mat3 × ℂ => ((x.1 i j : ℝ) : ℂ)) :=
    fun i j => Complex.continuous_ofReal.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
  have e' : ∀ i j : Fin 3, Continuous (fun x : Mat3 × Mat3 × ℂ => ((x.2.1 i j : ℝ) : ℂ)) :=
    fun i j => Complex.continuous_ofReal.comp ((continuous_apply j).comp ((continuous_apply i).comp
      (continuous_fst.comp continuous_snd)))
  have ξc : Continuous (fun x : Mat3 × Mat3 × ℂ => x.2.2) := continuous_snd.comp continuous_snd
  fun_prop

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
