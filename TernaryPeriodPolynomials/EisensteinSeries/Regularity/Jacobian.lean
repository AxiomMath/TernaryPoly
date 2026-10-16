module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Moebius
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.RingTheory.Complex
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section


/-!
# Hyperbolic measure, holomorphic change of variables and the Cayley transfer

* the real Jacobian of a holomorphic map is `|f'|²`, which gives the change of variables formula
  for integrals over `ℂ` of holomorphic injections (`lintegral_image_of_hasDerivAt`,
  `integral_image_of_hasDerivAt`, `integrableOn_image_iff_of_hasDerivAt`);
* the hyperbolic measure `hypMeasure = |Im w|^(-2) dA(w)` is given by its density
  (`lintegral_hypMeasure`, `integral_hypMeasure`), is invariant under the Möbius action of
  `GL₂(ℝ)`, under `w ↦ -w` and under complex conjugation, and splits into the two half planes;
* the Cayley transform `cay`/`icay` between the upper half plane and the unit disc, and the
  transfer of `hypMeasure` on the upper half plane to `4 (1 - |ζ|²)^(-2) dA(ζ)` on the disc.
-/

noncomputable section

open MeasureTheory Matrix

namespace TernaryPeriodPolynomials.Regularity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Open and measurable sets -/

theorem isOpen_offReal : IsOpen offReal := isOpen_ne_fun Complex.continuous_im continuous_const

theorem isOpen_upper : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im

theorem measurableSet_offReal : MeasurableSet offReal := isOpen_offReal.measurableSet

theorem measurableSet_upper : MeasurableSet upper := isOpen_upper.measurableSet

theorem upper_subset_offReal : upper ⊆ offReal := fun _ hz =>
  mem_offReal_iff.2 (mem_upper_iff.1 hz).ne'

/-! ### The real Jacobian of a holomorphic map -/

/-- An `ℝ`-linear endomorphism of `ℂ` that is multiplication by `c` has determinant `|c|²`. -/
private theorem det_eq_normSq_of_apply (L : ℂ →ₗ[ℝ] ℂ) (c : ℂ) (h : ∀ z, L z = z * c) :
    LinearMap.det L = Complex.normSq c := by
  have hL : L = Algebra.lmul ℝ ℂ c := by
    refine LinearMap.ext fun z => ?_
    rw [h z]
    exact mul_comm z c
  rw [hL]
  exact Algebra.norm_complex_apply c

/-- The determinant of the real-linear map `z ↦ z c` is `|c|²`. -/
theorem det_smulRight_restrictScalars (c : ℂ) :
    LinearMap.det ((((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ :
      ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq c :=
  det_eq_normSq_of_apply _ c fun _ => rfl

/-- The real derivative `ℂ →L[ℝ] ℂ` of a holomorphic map with complex derivative `c`. -/
private def realDeriv (c : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ

private theorem det_realDeriv (c : ℂ) : (realDeriv c).det = Complex.normSq c :=
  det_eq_normSq_of_apply _ c fun _ => rfl

private theorem abs_det_realDeriv (c : ℂ) : |(realDeriv c).det| = Complex.normSq c := by
  rw [det_realDeriv, abs_of_nonneg (Complex.normSq_nonneg c)]

private theorem hasFDerivWithinAt_realDeriv {f : ℂ → ℂ} {c z : ℂ} {s : Set ℂ}
    (h : HasDerivAt f c z) : HasFDerivWithinAt f (realDeriv c) s z :=
  (h.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

/-- Change of variables for the Lebesgue integral of a holomorphic injection: the Jacobian is
`|f'|²`. -/
theorem lintegral_image_of_hasDerivAt {s : Set ℂ} {f f' : ℂ → ℂ} (hs : MeasurableSet s)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z) (hinj : Set.InjOn f s) (φ : ℂ → ENNReal) :
    ∫⁻ z in f '' s, φ z = ∫⁻ z in s, ENNReal.ofReal (Complex.normSq (f' z)) * φ (f z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (f' := fun z => realDeriv (f' z)) (fun z hz => hasFDerivWithinAt_realDeriv (hf z hz)) hinj φ]
  refine setLIntegral_congr_fun hs fun z _ => ?_
  simp only [abs_det_realDeriv]

/-- Change of variables for the Bochner integral of a holomorphic injection: the Jacobian is
`|f'|²`. -/
theorem integral_image_of_hasDerivAt {s : Set ℂ} {f f' : ℂ → ℂ} (hs : MeasurableSet s)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z) (hinj : Set.InjOn f s) (φ : ℂ → F) :
    ∫ z in f '' s, φ z = ∫ z in s, Complex.normSq (f' z) • φ (f z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (f' := fun z => realDeriv (f' z)) (fun z hz => hasFDerivWithinAt_realDeriv (hf z hz)) hinj φ]
  refine setIntegral_congr_fun hs fun z _ => ?_
  simp only [abs_det_realDeriv]

/-- Integrability version of the change of variables for a holomorphic injection. -/
theorem integrableOn_image_iff_of_hasDerivAt {s : Set ℂ} {f f' : ℂ → ℂ} (hs : MeasurableSet s)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z) (hinj : Set.InjOn f s) (φ : ℂ → F) :
    IntegrableOn φ (f '' s) ↔ IntegrableOn (fun z => Complex.normSq (f' z) • φ (f z)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (f' := fun z => realDeriv (f' z)) (fun z hz => hasFDerivWithinAt_realDeriv (hf z hz)) hinj φ]
  simp only [abs_det_realDeriv]

/-! ### The density of the hyperbolic measure -/

private theorem measurable_hypDensity :
    Measurable fun w : ℂ => ENNReal.ofReal ((w.im ^ 2)⁻¹) := by
  fun_prop

private theorem hypDensity_lt_top (μ : Measure ℂ) :
    ∀ᵐ w ∂μ, ENNReal.ofReal ((w.im ^ 2)⁻¹) < ⊤ :=
  Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem toReal_hypDensity_smul (w : ℂ) (x : F) :
    (ENNReal.ofReal ((w.im ^ 2)⁻¹)).toReal • x = (w.im ^ 2)⁻¹ • x := by
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg w.im))]

/-- The hyperbolic measure restricted to a measurable subset of `ℂ ∖ ℝ` is `|Im w|^(-2) dA`
restricted to that subset. -/
theorem restrict_hypMeasure {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ offReal) :
    hypMeasure.restrict s =
      (volume.restrict s).withDensity fun w => ENNReal.ofReal ((w.im ^ 2)⁻¹) := by
  rw [hypMeasure, restrict_withDensity hs, Measure.restrict_restrict hs,
    Set.inter_eq_left.2 hsub]

/-- Lebesgue integrals against the hyperbolic measure, as integrals against area. -/
theorem lintegral_hypMeasure (φ : ℂ → ENNReal) :
    ∫⁻ w, φ w ∂hypMeasure = ∫⁻ w in offReal, ENNReal.ofReal ((w.im ^ 2)⁻¹) * φ w :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable (volume.restrict offReal)
    measurable_hypDensity (hypDensity_lt_top _) φ

/-- Bochner integrals against the hyperbolic measure, as integrals against area. -/
theorem integral_hypMeasure (φ : ℂ → F) :
    ∫ w, φ w ∂hypMeasure = ∫ w in offReal, (w.im ^ 2)⁻¹ • φ w := by
  rw [hypMeasure, integral_withDensity_eq_integral_toReal_smul measurable_hypDensity
    (hypDensity_lt_top _) φ]
  simp only [toReal_hypDensity_smul]

/-- The set integral version of `lintegral_hypMeasure` over a measurable subset of `ℂ ∖ ℝ`. -/
theorem setLIntegral_hypMeasure {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ offReal)
    (φ : ℂ → ENNReal) :
    ∫⁻ w in s, φ w ∂hypMeasure = ∫⁻ w in s, ENNReal.ofReal ((w.im ^ 2)⁻¹) * φ w := by
  rw [restrict_hypMeasure hs hsub]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable (volume.restrict s)
    measurable_hypDensity (hypDensity_lt_top _) φ

/-- The set integral version of `integral_hypMeasure` over a measurable subset of `ℂ ∖ ℝ`. -/
theorem setIntegral_hypMeasure {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ offReal)
    (φ : ℂ → F) :
    ∫ w in s, φ w ∂hypMeasure = ∫ w in s, (w.im ^ 2)⁻¹ • φ w := by
  rw [restrict_hypMeasure hs hsub, integral_withDensity_eq_integral_toReal_smul
    measurable_hypDensity (hypDensity_lt_top _) φ]
  simp only [toReal_hypDensity_smul]

/-- The hyperbolic measure lives on `ℂ ∖ ℝ`. -/
theorem ae_im_ne_zero : ∀ᵐ w ∂hypMeasure, w.im ≠ 0 := by
  have h : Measure.AbsolutelyContinuous hypMeasure (volume.restrict offReal) :=
    withDensity_absolutelyContinuous _ _
  have h2 : ∀ᵐ w ∂(volume.restrict offReal), w.im ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_offReal] with w hw
    exact mem_offReal_iff.1 hw
  exact ae_iff.2 (h (ae_iff.1 h2))

/-! ### Invariance of the hyperbolic measure -/

private theorem measurePreserving_of_lintegral {T : ℂ → ℂ} (hT : Measurable T)
    (h : ∀ φ : ℂ → ENNReal, ∫⁻ w, φ (T w) ∂hypMeasure = ∫⁻ w, φ w ∂hypMeasure) :
    MeasurePreserving T hypMeasure hypMeasure := by
  refine ⟨hT, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply hT hA]
  calc hypMeasure (T ⁻¹' A)
      = ∫⁻ w, (T ⁻¹' A).indicator (1 : ℂ → ENNReal) w ∂hypMeasure :=
        (lintegral_indicator_one (hT hA)).symm
    _ = ∫⁻ w, A.indicator (1 : ℂ → ENNReal) (T w) ∂hypMeasure :=
        lintegral_congr fun _ => rfl
    _ = ∫⁻ w, A.indicator (1 : ℂ → ENNReal) w ∂hypMeasure := h (A.indicator 1)
    _ = hypMeasure A := lintegral_indicator_one hA

private theorem lintegral_comp_of_hasDerivAt {f f' : ℂ → ℂ} (himg : f '' offReal = offReal)
    (hf : ∀ z ∈ offReal, HasDerivAt f (f' z) z) (hinj : Set.InjOn f offReal)
    (hdens : ∀ z ∈ offReal, ENNReal.ofReal (Complex.normSq (f' z)) *
        ENNReal.ofReal (((f z).im ^ 2)⁻¹) = ENNReal.ofReal ((z.im ^ 2)⁻¹))
    (φ : ℂ → ENNReal) : ∫⁻ w, φ (f w) ∂hypMeasure = ∫⁻ w, φ w ∂hypMeasure := by
  have h := lintegral_image_of_hasDerivAt measurableSet_offReal hf hinj
    (fun w => ENNReal.ofReal ((w.im ^ 2)⁻¹) * φ w)
  rw [himg] at h
  rw [lintegral_hypMeasure, lintegral_hypMeasure, h]
  refine setLIntegral_congr_fun measurableSet_offReal fun z hz => ?_
  show ENNReal.ofReal ((z.im ^ 2)⁻¹) * φ (f z) = ENNReal.ofReal (Complex.normSq (f' z)) *
    (ENNReal.ofReal (((f z).im ^ 2)⁻¹) * φ (f z))
  rw [← mul_assoc, hdens z hz]

private theorem jac_density_moeb (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    ENNReal.ofReal (Complex.normSq ((g.val.det : ℂ) / denom g w ^ 2)) *
      ENNReal.ofReal ((((moeb g w).im) ^ 2)⁻¹) = ENNReal.ofReal ((w.im ^ 2)⁻¹) := by
  have hD : g.val.det ≠ 0 := gl_det_ne_zero g
  have hn : Complex.normSq (denom g w) ≠ 0 := (Complex.normSq_pos.2 (denom_ne_zero g hw)).ne'
  rw [← ENNReal.ofReal_mul (Complex.normSq_nonneg _), im_moeb, map_div₀, map_pow,
    Complex.normSq_ofReal]
  congr 1
  field_simp

/-- The hyperbolic measure is invariant under the Möbius action of `GL₂(ℝ)`. -/
theorem measurePreserving_moeb (g : GL (Fin 2) ℝ) :
    MeasurePreserving (moeb g) hypMeasure hypMeasure :=
  measurePreserving_of_lintegral (measurable_moeb g) fun φ =>
    lintegral_comp_of_hasDerivAt (moeb_image_offReal g)
      (fun _ hw => hasDerivAt_moeb g (denom_ne_zero g (mem_offReal_iff.1 hw))) (moeb_injOn g)
      (fun _ hw => jac_density_moeb g (mem_offReal_iff.1 hw)) φ

private theorem measurePreserving_of_isometry (T : ℂ → ℂ) (e : ℂ ≃ₗᵢ[ℝ] ℂ)
    (hTe : ∀ w, e w = T w) (hab : ∀ w, |(T w).im| = |w.im|) :
    MeasurePreserving T hypMeasure hypMeasure := by
  obtain rfl : T = ⇑e := (funext hTe).symm
  have him : ∀ w, ((e w).im) ^ 2 = w.im ^ 2 := fun w => by
    rw [← sq_abs ((e w).im), hab w, sq_abs]
  have hpre : (⇑e) ⁻¹' offReal = offReal := by
    ext w
    show (e w).im ≠ 0 ↔ w.im ≠ 0
    rw [ne_eq, ne_eq, ← abs_eq_zero (a := (e w).im), hab w, abs_eq_zero]
  have hmp : MeasurePreserving (⇑e) volume volume := e.measurePreserving
  have hemb : MeasurableEmbedding (⇑e) := e.toHomeomorph.measurableEmbedding
  refine measurePreserving_of_lintegral e.continuous.measurable fun φ => ?_
  rw [lintegral_hypMeasure, lintegral_hypMeasure]
  have h := hmp.setLIntegral_comp_preimage_emb hemb
    (fun w => ENNReal.ofReal ((w.im ^ 2)⁻¹) * φ w) offReal
  rw [hpre] at h
  rw [← h]
  refine setLIntegral_congr_fun measurableSet_offReal fun w _ => ?_
  show ENNReal.ofReal ((w.im ^ 2)⁻¹) * φ (e w) = ENNReal.ofReal (((e w).im ^ 2)⁻¹) * φ (e w)
  rw [him w]

/-- The hyperbolic measure is invariant under `w ↦ -w`. -/
theorem measurePreserving_neg : MeasurePreserving (fun w : ℂ => -w) hypMeasure hypMeasure :=
  measurePreserving_of_isometry _ (LinearIsometryEquiv.neg ℝ) (fun _ => rfl) fun w => by simp

/-- The hyperbolic measure is invariant under complex conjugation. -/
theorem measurePreserving_conj : MeasurePreserving (starRingEnd ℂ) hypMeasure hypMeasure :=
  measurePreserving_of_isometry _ Complex.conjLIE (fun _ => rfl) fun w => by simp

/-! ### Splitting into the two half planes -/

private theorem measurableEmbedding_neg' : MeasurableEmbedding (fun w : ℂ => -w) :=
  measurableEmbedding_neg

private theorem compl_upper_ae_eq :
    (upperᶜ : Set ℂ) =ᵐ[hypMeasure] ((fun w : ℂ => -w) ⁻¹' upper) := by
  filter_upwards [ae_im_ne_zero] with w hw
  apply propext
  change ¬ (0 < w.im) ↔ 0 < (-w).im
  rw [Complex.neg_im, neg_pos, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h hw, le_of_lt⟩

/-- A Lebesgue integral against the hyperbolic measure splits into the two half planes. -/
theorem lintegral_hypMeasure_split (φ : ℂ → ENNReal) :
    ∫⁻ w, φ w ∂hypMeasure =
      ∫⁻ z in upper, φ z ∂hypMeasure + ∫⁻ z in upper, φ (-z) ∂hypMeasure := by
  have h := measurePreserving_neg.setLIntegral_comp_preimage_emb measurableEmbedding_neg'
    (fun b => φ (-b)) upper
  have h' : ∫⁻ x in (fun w : ℂ => -w) ⁻¹' upper, φ x ∂hypMeasure
      = ∫⁻ z in upper, φ (-z) ∂hypMeasure := by
    simpa only [neg_neg] using h
  rw [← lintegral_add_compl (μ := hypMeasure) φ measurableSet_upper,
    setLIntegral_congr compl_upper_ae_eq, h']

/-- A Bochner integral against the hyperbolic measure splits into the two half planes. -/
theorem integral_hypMeasure_split {φ : ℂ → F} (hφ : Integrable φ hypMeasure) :
    ∫ w, φ w ∂hypMeasure = ∫ z in upper, φ z ∂hypMeasure + ∫ z in upper, φ (-z) ∂hypMeasure := by
  have h := measurePreserving_neg.setIntegral_preimage_emb measurableEmbedding_neg'
    (fun b => φ (-b)) upper
  have h' : ∫ x in (fun w : ℂ => -w) ⁻¹' upper, φ x ∂hypMeasure
      = ∫ z in upper, φ (-z) ∂hypMeasure := by
    simpa only [neg_neg] using h
  rw [← integral_add_compl measurableSet_upper hφ, setIntegral_congr_set compl_upper_ae_eq, h']

/-! ### The Cayley transform -/

private theorem ne_one_of_norm_lt_one {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ζ ≠ 1 := by
  rintro rfl
  simp at hζ

private theorem ne_one_of_mem_ball {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) : ζ ≠ 1 :=
  ne_one_of_norm_lt_one (mem_ball_zero_iff.1 hζ)

private theorem add_I_ne_zero_of_mem_upper {z : ℂ} (hz : z ∈ upper) : z + Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hz' : 0 < z.im := mem_upper_iff.1 hz
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith

theorem icay_add_I {ζ : ℂ} (hζ : ζ ≠ 1) : icay ζ + Complex.I = 2 * Complex.I / (1 - ζ) := by
  have h : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
  rw [icay]
  field_simp
  ring

theorem im_icay {ζ : ℂ} (_hζ : ζ ≠ 1) :
    (icay ζ).im = (1 - ‖ζ‖ ^ 2) / ‖1 - ζ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, icay, Complex.div_im, ← sub_div]
  congr 1
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply]
  ring

theorem icay_mem_upper {ζ : ℂ} (hζ : ‖ζ‖ < 1) : icay ζ ∈ upper := by
  have h1 : ζ ≠ 1 := ne_one_of_norm_lt_one hζ
  have hb : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hN : 0 < ‖1 - ζ‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h1))) 2
  refine mem_upper_iff.2 ?_
  rw [im_icay h1]
  exact div_pos hb hN

theorem norm_cay_lt_one {z : ℂ} (hz : z ∈ upper) : ‖cay z‖ < 1 := by
  have hz' : 0 < z.im := mem_upper_iff.1 hz
  have hpos : 0 < ‖z + Complex.I‖ := norm_pos_iff.2 (add_I_ne_zero_of_mem_upper hz)
  rw [cay, norm_div, div_lt_one hpos]
  by_contra hcon
  have h1 := mul_self_le_mul_self (norm_nonneg _) (not_lt.1 hcon)
  have h2 : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im]
    nlinarith
  nlinarith

theorem cay_icay {ζ : ℂ} (hζ : ζ ≠ 1) : cay (icay ζ) = ζ := by
  have h : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hsub : icay ζ - Complex.I = 2 * Complex.I * ζ / (1 - ζ) := by
    rw [icay]
    field_simp
    ring
  rw [cay, hsub, icay_add_I hζ]
  field_simp

theorem icay_cay {z : ℂ} (hz : z + Complex.I ≠ 0) : icay (cay z) = z := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h1 : (1 : ℂ) + cay z = 2 * z / (z + Complex.I) := by
    rw [cay]
    field_simp
    ring
  have h2 : (1 : ℂ) - cay z = 2 * Complex.I / (z + Complex.I) := by
    rw [cay]
    field_simp
    ring
  rw [icay, h1, h2]
  field_simp

theorem icay_zero : icay 0 = Complex.I := by simp [icay]

theorem cay_I : cay Complex.I = 0 := by simp [cay]

theorem hasDerivAt_icay {ζ : ℂ} (hζ : ζ ≠ 1) :
    HasDerivAt icay (2 * Complex.I / (1 - ζ) ^ 2) ζ := by
  have h : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
  have h1 : HasDerivAt (fun y : ℂ => Complex.I * (1 + y)) (Complex.I * 1) ζ :=
    ((hasDerivAt_id' ζ).const_add 1).const_mul Complex.I
  have h2 : HasDerivAt (fun y : ℂ => 1 - y) (-1) ζ := (hasDerivAt_id' ζ).const_sub 1
  refine (h1.fun_div h2 h).congr_deriv ?_
  ring

theorem differentiableOn_icay : DifferentiableOn ℂ icay (Metric.ball 0 1) := fun _ hζ =>
  (hasDerivAt_icay (ne_one_of_mem_ball hζ)).differentiableAt.differentiableWithinAt

theorem differentiableOn_cay : DifferentiableOn ℂ cay upper := by
  intro z hz
  have hne : z + Complex.I ≠ 0 := add_I_ne_zero_of_mem_upper hz
  have h1 : HasDerivAt (fun y : ℂ => y - Complex.I) 1 z :=
    (hasDerivAt_id' z).sub_const Complex.I
  have h2 : HasDerivAt (fun y : ℂ => y + Complex.I) 1 z :=
    (hasDerivAt_id' z).add_const Complex.I
  exact (h1.fun_div h2 hne).differentiableAt.differentiableWithinAt

theorem icay_image_ball : icay '' Metric.ball 0 1 = upper := by
  ext z
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    exact icay_mem_upper (mem_ball_zero_iff.1 hζ)
  · intro hz
    exact ⟨cay z, mem_ball_zero_iff.2 (norm_cay_lt_one hz),
      icay_cay (add_I_ne_zero_of_mem_upper hz)⟩

theorem icay_injOn : Set.InjOn icay (Metric.ball 0 1) := by
  intro a ha b hb hab
  have h := congrArg cay hab
  rwa [cay_icay (ne_one_of_mem_ball ha), cay_icay (ne_one_of_mem_ball hb)] at h

/-! ### Transfer to the unit disc -/

private theorem disc_density {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    Complex.normSq (2 * Complex.I / (1 - ζ) ^ 2) * ((icay ζ).im ^ 2)⁻¹ =
      4 / (1 - ‖ζ‖ ^ 2) ^ 2 := by
  have h1 : ζ ≠ 1 := ne_one_of_norm_lt_one hζ
  have hN : ‖1 - ζ‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm h1))
  have hbpos : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hb : 1 - ‖ζ‖ ^ 2 ≠ 0 := hbpos.ne'
  have h2 : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq_apply]
  rw [map_div₀, map_mul, map_pow, Complex.normSq_I, h2, ← Complex.sq_norm (1 - ζ), im_icay h1]
  field_simp

/-- The hyperbolic measure on the upper half plane transfers to `4 (1 - |ζ|²)^(-2) dA(ζ)` on
the unit disc under the Cayley transform. -/
theorem lintegral_upper_eq_disc (φ : ℂ → ENNReal) :
    ∫⁻ z in upper, φ z ∂hypMeasure =
      ∫⁻ ζ in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2) * φ (icay ζ) := by
  rw [setLIntegral_hypMeasure measurableSet_upper upper_subset_offReal, ← icay_image_ball,
    lintegral_image_of_hasDerivAt (s := Metric.ball (0 : ℂ) 1) (f := icay)
      Metric.isOpen_ball.measurableSet
      (fun _ hζ => hasDerivAt_icay (ne_one_of_mem_ball hζ)) icay_injOn]
  refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet fun ζ hζ => ?_
  show ENNReal.ofReal (Complex.normSq (2 * Complex.I / (1 - ζ) ^ 2)) *
    (ENNReal.ofReal (((icay ζ).im ^ 2)⁻¹) * φ (icay ζ)) =
      ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2) * φ (icay ζ)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
    disc_density (mem_ball_zero_iff.1 hζ)]

/-- The Bochner version of `lintegral_upper_eq_disc`. -/
theorem integral_upper_eq_disc (φ : ℂ → F) :
    ∫ z in upper, φ z ∂hypMeasure =
      ∫ ζ in Metric.ball (0 : ℂ) 1, (4 / (1 - ‖ζ‖ ^ 2) ^ 2) • φ (icay ζ) := by
  rw [setIntegral_hypMeasure measurableSet_upper upper_subset_offReal, ← icay_image_ball,
    integral_image_of_hasDerivAt (s := Metric.ball (0 : ℂ) 1) (f := icay)
      Metric.isOpen_ball.measurableSet
      (fun _ hζ => hasDerivAt_icay (ne_one_of_mem_ball hζ)) icay_injOn]
  refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun ζ hζ => ?_
  show Complex.normSq (2 * Complex.I / (1 - ζ) ^ 2) • (((icay ζ).im ^ 2)⁻¹ • φ (icay ζ)) = _
  rw [smul_smul, disc_density (mem_ball_zero_iff.1 hζ)]

/-- Integrability on the upper half plane against the hyperbolic measure is integrability of the
transferred function on the unit disc. -/
theorem integrableOn_upper_iff (φ : ℂ → F) :
    IntegrableOn φ upper hypMeasure ↔
      IntegrableOn (fun ζ => (4 / (1 - ‖ζ‖ ^ 2) ^ 2) • φ (icay ζ)) (Metric.ball 0 1) := by
  have h1 : IntegrableOn φ upper hypMeasure ↔ IntegrableOn (fun z => (z.im ^ 2)⁻¹ • φ z) upper := by
    unfold IntegrableOn
    rw [restrict_hypMeasure measurableSet_upper upper_subset_offReal,
      integrable_withDensity_iff_integrable_smul' measurable_hypDensity (hypDensity_lt_top _)]
    simp only [toReal_hypDensity_smul]
  rw [h1, ← icay_image_ball,
    integrableOn_image_iff_of_hasDerivAt (s := Metric.ball (0 : ℂ) 1) (f := icay)
      Metric.isOpen_ball.measurableSet
      (fun _ hζ => hasDerivAt_icay (ne_one_of_mem_ball hζ)) icay_injOn]
  refine integrableOn_congr_fun (fun ζ hζ => ?_) Metric.isOpen_ball.measurableSet
  show Complex.normSq (2 * Complex.I / (1 - ζ) ^ 2) • (((icay ζ).im ^ 2)⁻¹ • φ (icay ζ)) = _
  rw [smul_smul, disc_density (mem_ball_zero_iff.1 hζ)]

end TernaryPeriodPolynomials.Regularity

end
