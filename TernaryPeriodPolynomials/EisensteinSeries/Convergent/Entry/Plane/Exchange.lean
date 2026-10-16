module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourcePackage
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Uniform

@[expose] public section


/-!
# Exchanging a parameter integral with the plane integral cochain

The coefficients of the twisted pullback of the seed `ω_h` are `h(τ_p)` times a continuous kernel
(`coeff_twPull_seed_scale`, `planeIntG_eq_tau`), so `planeIntG` is linear in `h` (`planeIntG_const_mul`) and a
parameter integral of `planeIntG n (h_v)` over a finite-adelic variable `v` can be exchanged with the integral over
the Gram triangle as soon as `(v, z) ↦ h_v(z)` is measurable and locally (in `z`) dominated by an integrable function
of `v` (`planeIntG_exchange`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem formPair_seed_scale (n : ℕ) (h : ℂ → ℂ) (G Q₁ Q₂ : Mat3) :
    formPair (seedForm n h) G Q₁ Q₂ =
      MvPolynomial.C (h (gramPlaneTau G)) * formPair (seedForm n (fun _ => 1)) G Q₁ Q₂ := by
  rw [formPair_seedForm, formPair_seedForm]
  simp only [one_mul, map_mul]
  ring

/-- The coefficients of the twisted pullback of the seed are `h(τ)` times the coefficients for `h ≡ 1`. -/
theorem coeff_twPull_seed_scale (n : ℕ) (h : ℂ → ℂ) (M P Q₁ Q₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    (twPull (seedForm n h) M P Q₁ Q₂).coeff κ =
      h (gramPlaneTau (M * P * Mᵀ)) *
        (twPull (seedForm n (fun _ => 1)) M P Q₁ Q₂).coeff κ := by
  unfold twPull
  rw [formPair_seed_scale, rho_C_mul, MvPolynomial.coeff_C_mul]

theorem planeIntG_const_mul (n : ℕ) (c : ℂ) (h : ℂ → ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    planeIntG n (fun z => c * h z) M Γ₀ Γ₁ Γ₂ κ = c * planeIntG n h M Γ₀ Γ₁ Γ₂ κ := by
  unfold planeIntG
  have : ∀ p : ℝ × ℝ, (twPull (seedForm n (fun z => c * h z)) M (affTri Γ₀ Γ₁ Γ₂ p)
      (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ = c * (twPull (seedForm n h) M (affTri Γ₀ Γ₁ Γ₂ p)
      (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ := by
    intro p
    rw [coeff_twPull_seed_scale n (fun z => c * h z), coeff_twPull_seed_scale n h]
    ring
  simp_rw [this]
  exact integral_const_mul c _

theorem continuousOn_coeff_twPull (n : ℕ) (h : ℂ → ℂ) (hh : ContinuousOn h {z : ℂ | 0 < z.im})
    (M : Mat3) (hM : M.det ≠ 0) (Γ₀ Γ₁ Γ₂ : Mat3) (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef)
    (κ : Fin 3 →₀ ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (twPull (seedForm n h) M (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ) stdTriangle := by
  set Γ'₀ := M * Γ₀ * Mᵀ with hΓ'₀
  set Γ'₁ := M * Γ₁ * Mᵀ with hΓ'₁
  set Γ'₂ := M * Γ₂ * Mᵀ with hΓ'₂
  have q₀ : Γ'₀.PosDef := posDef_congr p₀ hM
  have q₁ : Γ'₁.PosDef := posDef_congr p₁ hM
  have q₂ : Γ'₂.PosDef := posDef_congr p₂ hM
  have hcond := affTri_mem_cholDomain q₀ q₁ q₂
  have hdom : ∀ p ∈ stdTriangle, affTri Γ'₀ Γ'₁ Γ'₂ p ∈ gramDomain := fun p hp =>
    cholDomain_subset_gramDomain (posDef_transpose (posDef_affTri q₀ q₁ q₂ hp)) (hcond p hp)
  have hQ1 : M * (Γ₁ - Γ₀) * Mᵀ = Γ'₁ - Γ'₀ := by
    simp only [hΓ'₁, hΓ'₀, Matrix.mul_sub, Matrix.sub_mul]
  have hQ2 : M * (Γ₂ - Γ₀) * Mᵀ = Γ'₂ - Γ'₀ := by
    simp only [hΓ'₂, hΓ'₀, Matrix.mul_sub, Matrix.sub_mul]
  have hP : ∀ p, M * affTri Γ₀ Γ₁ Γ₂ p * Mᵀ = affTri Γ'₀ Γ'₁ Γ'₂ p := fun p =>
    (affTri_congr M Γ₀ Γ₁ Γ₂ p).symm
  have hQs1 : (Γ'₁ - Γ'₀)ᵀ = Γ'₁ - Γ'₀ := by
    rw [Matrix.transpose_sub, posDef_transpose q₁, posDef_transpose q₀]
  have hQs2 : (Γ'₂ - Γ'₀)ᵀ = Γ'₂ - Γ'₀ := by
    rw [Matrix.transpose_sub, posDef_transpose q₂, posDef_transpose q₀]
  have hform : ∀ ν, ContinuousOn (fun p : ℝ × ℝ => (formPair (seedForm n h)
      (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)).coeff ν) stdTriangle := by
    intro ν
    exact continuousOn_coeff_formPair_comp n h hh _ _ _ (continuous_affTri Γ'₀ Γ'₁ Γ'₂).continuousOn
      continuousOn_const continuousOn_const
      (fun p hp => ⟨hdom p hp, posDef_transpose (posDef_affTri q₀ q₁ q₂ hp), hQs1, hQs2⟩) ν
  have hsum : ∀ p : ℝ × ℝ, (twPull (seedForm n h) M (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ =
      ∑ ν ∈ degSet n, (formPair (seedForm n h)
        (affTri Γ'₀ Γ'₁ Γ'₂ p) (Γ'₁ - Γ'₀) (Γ'₂ - Γ'₀)).coeff ν *
        (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
    intro p
    unfold twPull
    rw [hP, hQ1, hQ2]
    exact coeff_rho_eq_sum _ n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
      (isHomogeneous_formPair_seed n h _ _ _) m' hm') κ
  simp_rw [hsum]
  exact continuousOn_finsetSum _ fun ν _ => (hform ν).mul continuousOn_const

/-- The kernel of the plane integral cochain: the coefficient of the twisted pullback of the seed with `h ≡ 1`. -/
def planeKernel (n : ℕ) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) (p : ℝ × ℝ) : ℂ :=
  (twPull (seedForm n (fun _ => 1)) M (affTri Γ₀ Γ₁ Γ₂ p) (Γ₁ - Γ₀) (Γ₂ - Γ₀)).coeff κ

/-- The point of the upper half plane carried by a point of the Gram triangle. -/
def planeTauPt (M Γ₀ Γ₁ Γ₂ : Mat3) (p : ℝ × ℝ) : ℂ := gramPlaneTau (M * affTri Γ₀ Γ₁ Γ₂ p * Mᵀ)

theorem planeIntG_eq_tau (n : ℕ) (h : ℂ → ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    planeIntG n h M Γ₀ Γ₁ Γ₂ κ =
      ∫ p in stdTriangle, h (planeTauPt M Γ₀ Γ₁ Γ₂ p) * planeKernel n M Γ₀ Γ₁ Γ₂ κ p := by
  unfold planeIntG
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact coeff_twPull_seed_scale n h _ _ _ _ κ

theorem planeTauPt_mem (M : Mat3) (hM : M.det ≠ 0) {Γ₀ Γ₁ Γ₂ : Mat3} (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef)
    (p₂ : Γ₂.PosDef) {p : ℝ × ℝ} (hp : p ∈ stdTriangle) :
    0 < (planeTauPt M Γ₀ Γ₁ Γ₂ p).im := by
  have q₀ : (M * Γ₀ * Mᵀ).PosDef := posDef_congr p₀ hM
  have q₁ : (M * Γ₁ * Mᵀ).PosDef := posDef_congr p₁ hM
  have q₂ : (M * Γ₂ * Mᵀ).PosDef := posDef_congr p₂ hM
  have hcond := affTri_mem_cholDomain q₀ q₁ q₂
  have hdom := cholDomain_subset_gramDomain (posDef_transpose (posDef_affTri q₀ q₁ q₂ hp)) (hcond p hp)
  unfold planeTauPt
  rw [affTri_congr M Γ₀ Γ₁ Γ₂ p |>.symm]
  exact gramPlaneTau_im_pos_of_domain hdom

theorem continuousOn_planeTauPt (M : Mat3) (hM : M.det ≠ 0) {Γ₀ Γ₁ Γ₂ : Mat3} (p₀ : Γ₀.PosDef)
    (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) :
    ContinuousOn (planeTauPt M Γ₀ Γ₁ Γ₂) stdTriangle := by
  have q₀ : (M * Γ₀ * Mᵀ).PosDef := posDef_congr p₀ hM
  have q₁ : (M * Γ₁ * Mᵀ).PosDef := posDef_congr p₁ hM
  have q₂ : (M * Γ₂ * Mᵀ).PosDef := posDef_congr p₂ hM
  have hcond := affTri_mem_cholDomain q₀ q₁ q₂
  have hdom : ∀ p ∈ stdTriangle, affTri (M * Γ₀ * Mᵀ) (M * Γ₁ * Mᵀ) (M * Γ₂ * Mᵀ) p ∈ gramDomain :=
    fun p hp => cholDomain_subset_gramDomain (posDef_transpose (posDef_affTri q₀ q₁ q₂ hp)) (hcond p hp)
  have hc : ContinuousOn (fun p : ℝ × ℝ => affTri (M * Γ₀ * Mᵀ) (M * Γ₁ * Mᵀ) (M * Γ₂ * Mᵀ) p) stdTriangle :=
    (continuous_affTri _ _ _).continuousOn
  have := contDiffOn_gramPlaneTau.continuousOn.comp hc hdom
  refine this.congr fun p _ => ?_
  simp only [Function.comp_apply, planeTauPt, affTri_congr M Γ₀ Γ₁ Γ₂ p]

theorem planeIntG_exchange {V : Type*} [MeasurableSpace V] (μ : Measure V) [SigmaFinite μ]
    (n : ℕ) (hv : V → ℂ → ℂ) (M : Mat3) (hM : M.det ≠ 0) {Γ₀ Γ₁ Γ₂ : Mat3}
    (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ)
    (hmeas : Measurable (fun w : V × {z : ℂ // 0 < z.im} => hv w.1 w.2.1))
    (hdom : ∀ Z : Set ℂ, IsCompact Z → Z ⊆ {z : ℂ | 0 < z.im} →
      ∃ φ : V → ℝ, Integrable φ μ ∧ ∀ v, ∀ z ∈ Z, ‖hv v z‖ ≤ φ v) :
    Integrable (fun v => planeIntG n (hv v) M Γ₀ Γ₁ Γ₂ κ) μ ∧
    ∫ v, planeIntG n (hv v) M Γ₀ Γ₁ Γ₂ κ ∂μ =
      planeIntG n (fun z => ∫ v, hv v z ∂μ) M Γ₀ Γ₁ Γ₂ κ := by
  set τ := planeTauPt M Γ₀ Γ₁ Γ₂ with hτdef
  set K := planeKernel n M Γ₀ Γ₁ Γ₂ κ with hKdef
  have hK : ContinuousOn K stdTriangle :=
    continuousOn_coeff_twPull n (fun _ => 1) continuousOn_const M hM Γ₀ Γ₁ Γ₂ p₀ p₁ p₂ κ
  have hτ : ContinuousOn τ stdTriangle := continuousOn_planeTauPt M hM p₀ p₁ p₂
  have him : ∀ p : ↥stdTriangle, 0 < (τ p.1).im := fun p => planeTauPt_mem M hM p₀ p₁ p₂ p.2
  set Θ : ↥stdTriangle → {z : ℂ // 0 < z.im} := fun p => ⟨τ p.1, him p⟩ with hΘ
  have hΘc : Continuous Θ := (hτ.domRestrict).subtype_mk _
  have hKc : Continuous (fun p : ↥stdTriangle => K p.1) := hK.domRestrict
  set f : V → ↥stdTriangle → ℂ := fun v p => hv v (τ p.1) * K p.1 with hf
  set ν : Measure ↥stdTriangle := Measure.comap Subtype.val (volume : Measure (ℝ × ℝ)) with hν
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, (MeasurableEmbedding.subtype_coe measurableSet_stdTriangle).comap_apply, Set.image_univ,
      Subtype.range_coe]
    exact isCompact_stdTriangle.measure_lt_top
  have hplane : ∀ v, planeIntG n (hv v) M Γ₀ Γ₁ Γ₂ κ = ∫ p : ↥stdTriangle, f v p ∂ν := by
    intro v
    rw [planeIntG_eq_tau, (integral_subtype_comap measurableSet_stdTriangle _).symm]
  have hplane' : planeIntG n (fun z => ∫ v, hv v z ∂μ) M Γ₀ Γ₁ Γ₂ κ =
      ∫ p : ↥stdTriangle, ∫ v, f v p ∂μ ∂ν := by
    rw [planeIntG_eq_tau, (integral_subtype_comap measurableSet_stdTriangle _).symm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hf]
    rw [integral_mul_const]
  have hmeasf : Measurable (Function.uncurry f) := by
    have h1 : Measurable (fun w : V × ↥stdTriangle => hv w.1 (τ w.2.1)) :=
      hmeas.comp (measurable_fst.prodMk (hΘc.measurable.comp measurable_snd))
    exact h1.mul (hKc.measurable.comp measurable_snd)
  obtain ⟨C, hC⟩ := isCompact_stdTriangle.exists_bound_of_continuousOn hK
  have hZ : IsCompact (τ '' stdTriangle) := isCompact_stdTriangle.image_of_continuousOn hτ
  have hZH : τ '' stdTriangle ⊆ {z : ℂ | 0 < z.im} := by
    rintro _ ⟨p, hp, rfl⟩
    exact planeTauPt_mem M hM p₀ p₁ p₂ hp
  obtain ⟨φ, hφ, hφb⟩ := hdom _ hZ hZH
  have hF : Integrable (Function.uncurry f) (μ.prod ν) := by
    have hbd : Integrable (fun w : V × ↥stdTriangle => φ w.1 * C) (μ.prod ν) :=
      hφ.mul_prod (integrable_const C)
    refine hbd.mono' hmeasf.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.uncurry, hf, norm_mul]
    exact mul_le_mul (hφb w.1 _ ⟨w.2.1, w.2.2, rfl⟩) (hC w.2.1 w.2.2) (norm_nonneg _)
      ((norm_nonneg _).trans (hφb w.1 _ ⟨w.2.1, w.2.2, rfl⟩))
  refine ⟨?_, ?_⟩
  · simp_rw [hplane]
    exact hF.integral_prod_left
  · simp_rw [hplane]
    rw [hplane']
    exact integral_integral_swap hF

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
