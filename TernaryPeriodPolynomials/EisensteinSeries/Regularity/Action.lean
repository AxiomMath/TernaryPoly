module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Bergman
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.FiniteModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.AbstractIrreducibility

@[expose] public section


/-!
# The unitary action of `GL₂(𝔸)` on the Bergman space

A real matrix `g` acts on functions `F : ℂ → E` by
`(actFun k g F) w = autFactor k g w • F (g⁻¹ w)` (and by `0` on the real axis).  This preserves
the Bergman space and its norm, giving the unitary representation `realRep` of `GL₂(ℝ)` on
`BergmanSpace k E`.  A unitary representation `σ` of `GL₂(𝔸_f)` on `E` acts pointwise
(`finRep`) and commutes with `realRep`.  For a finite-adelic model `M`, the product of the two
is the unitary representation `bergmanRep M` of `GL₂(𝔸)` on `BergmanSpace k M.E`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic

namespace TernaryPeriodPolynomials.Regularity

section Real

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The action `F ↦ (w ↦ autFactor k g w • F (g⁻¹ w))` of a real matrix on functions on `ℂ`,
extended by zero to the real axis. -/
def actFun (k : ℕ) (g : GL (Fin 2) ℝ) (F : ℂ → E) : ℂ → E :=
  fun w => if w.im = 0 then 0 else autFactor k g w • F (moeb g⁻¹ w)

theorem actFun_apply_of_im_ne_zero (g : GL (Fin 2) ℝ) (F : ℂ → E) {w : ℂ} (hw : w.im ≠ 0) :
    actFun k g F w = autFactor k g w • F (moeb g⁻¹ w) :=
  ite_eq_right hw

theorem actFun_apply_of_im_eq_zero (g : GL (Fin 2) ℝ) (F : ℂ → E) {w : ℂ} (hw : w.im = 0) :
    actFun k g F w = 0 :=
  ite_eq_left hw

theorem actFun_add (g : GL (Fin 2) ℝ) (F G : ℂ → E) :
    actFun k g (F + G) = actFun k g F + actFun k g G := by
  funext w
  by_cases hw : w.im = 0
  · rw [Pi.add_apply, actFun_apply_of_im_eq_zero g (F + G) hw, actFun_apply_of_im_eq_zero g F hw,
      actFun_apply_of_im_eq_zero g G hw, add_zero]
  · rw [Pi.add_apply, actFun_apply_of_im_ne_zero g (F + G) hw, actFun_apply_of_im_ne_zero g F hw,
      actFun_apply_of_im_ne_zero g G hw, Pi.add_apply, smul_add]

theorem actFun_smul (g : GL (Fin 2) ℝ) (c : ℂ) (F : ℂ → E) :
    actFun k g (c • F) = c • actFun k g F := by
  funext w
  by_cases hw : w.im = 0
  · rw [Pi.smul_apply, actFun_apply_of_im_eq_zero g (c • F) hw,
      actFun_apply_of_im_eq_zero g F hw, smul_zero]
  · rw [Pi.smul_apply, actFun_apply_of_im_ne_zero g (c • F) hw, actFun_apply_of_im_ne_zero g F hw,
      Pi.smul_apply]
    exact smul_comm _ _ _

theorem actFun_mul (g h : GL (Fin 2) ℝ) (F : ℂ → E) (w : ℂ) :
    actFun k (g * h) F w = actFun k g (actFun k h F) w := by
  by_cases hw : w.im = 0
  · rw [actFun_apply_of_im_eq_zero (g * h) F hw, actFun_apply_of_im_eq_zero g (actFun k h F) hw]
  · have hw' : (moeb g⁻¹ w).im ≠ 0 := moeb_im_ne_zero _ hw
    rw [actFun_apply_of_im_ne_zero (g * h) F hw, actFun_apply_of_im_ne_zero g (actFun k h F) hw,
      actFun_apply_of_im_ne_zero h F hw', autFactor_mul k g h hw, mul_inv_rev, moeb_mul _ _ hw,
      mul_smul]

theorem actFun_one_apply (F : ℂ → E) (hF : ∀ w : ℂ, w.im = 0 → F w = 0) (w : ℂ) :
    actFun k 1 F w = F w := by
  by_cases hw : w.im = 0
  · rw [actFun_apply_of_im_eq_zero 1 F hw, hF w hw]
  · rw [actFun_apply_of_im_ne_zero 1 F hw, autFactor_one, inv_one, moeb_one, one_smul]

theorem norm_actFun_sq_mul (g : GL (Fin 2) ℝ) (F : ℂ → E) {w : ℂ} (hw : w.im ≠ 0) :
    ‖actFun k g F w‖ ^ 2 * |w.im| ^ k = ‖F (moeb g⁻¹ w)‖ ^ 2 * |(moeb g⁻¹ w).im| ^ k := by
  rw [actFun_apply_of_im_ne_zero g F hw, norm_smul, mul_pow, ← norm_autFactor_sq k g hw]
  ring

omit [NormedSpace ℂ E] in
/-- The density `ofReal (‖F w‖² |Im w|^k)` integrated against `hypMeasure` by `bergmanNormSq`. -/
def bergmanDensity (k : ℕ) (F : ℂ → E) (w : ℂ) : ENNReal :=
  ENNReal.ofReal (‖F w‖ ^ 2 * |w.im| ^ k)

omit [NormedSpace ℂ E] in
theorem bergmanNormSq_eq_lintegral (F : ℂ → E) :
    bergmanNormSq k F = ∫⁻ w, bergmanDensity k F w ∂hypMeasure :=
  rfl

omit [NormedSpace ℂ E] in
theorem aemeasurable_bergmanDensity {F : ℂ → E} (hF : ContinuousOn F offReal) :
    AEMeasurable (bergmanDensity k F) hypMeasure := by
  have h : ContinuousOn (bergmanDensity k F) offReal :=
    ENNReal.continuous_ofReal.comp_continuousOn (BergmanAux.continuousOn_weight (k := k) hF)
  exact (h.aemeasurable (μ := volume) measurableSet_offReal).mono_ac BergmanAux.hyp_ac

theorem bergmanNormSq_actFun (g : GL (Fin 2) ℝ) {F : ℂ → E} (hF : ContinuousOn F offReal) :
    bergmanNormSq k (actFun k g F) = bergmanNormSq k F := by
  have hmp := measurePreserving_moeb g⁻¹
  have hφm : AEMeasurable (bergmanDensity k F) (Measure.map (moeb g⁻¹) hypMeasure) := by
    rw [hmp.map_eq]
    exact aemeasurable_bergmanDensity hF
  have h1 : bergmanNormSq k (actFun k g F) =
      ∫⁻ w, bergmanDensity k F (moeb g⁻¹ w) ∂hypMeasure := by
    rw [bergmanNormSq_eq_lintegral]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_im_ne_zero] with w hw
    unfold bergmanDensity
    rw [norm_actFun_sq_mul g F hw]
  have h2 : ∫⁻ w, bergmanDensity k F (moeb g⁻¹ w) ∂hypMeasure =
      ∫⁻ w, bergmanDensity k F w ∂(Measure.map (moeb g⁻¹) hypMeasure) :=
    (lintegral_map' hφm (measurable_moeb g⁻¹).aemeasurable).symm
  rw [h1, h2, hmp.map_eq, bergmanNormSq_eq_lintegral]

theorem actFun_isBergman (g : GL (Fin 2) ℝ) {F : ℂ → E} (hF : IsBergman k F) :
    IsBergman k (actFun k g F) where
  holo := by
    have hd : DifferentiableOn ℂ (fun w => autFactor k g w • F (moeb g⁻¹ w)) offReal :=
      (differentiableOn_autFactor k g).smul
        (hF.holo.comp (differentiableOn_moeb g⁻¹) fun w hw => moeb_mem_offReal g⁻¹ hw)
    exact hd.congr fun w hw => actFun_apply_of_im_ne_zero g F hw
  vanish w hw := actFun_apply_of_im_eq_zero g F hw
  finite := by
    rw [bergmanNormSq_actFun g hF.holo.continuousOn]
    exact hF.finite

theorem actFun_mem (g : GL (Fin 2) ℝ) {F : ℂ → E} (hF : F ∈ bergmanSubmodule k E) :
    actFun k g F ∈ bergmanSubmodule k E :=
  actFun_isBergman g hF

variable (k E) in
/-- The action of a real matrix on the Bergman space, as a linear map. -/
def realOp (g : GL (Fin 2) ℝ) : BergmanSpace k E →ₗ[ℂ] BergmanSpace k E where
  toFun F := BergmanSpace.mk (actFun k g F) (actFun_isBergman g F.isBergman).holo
    (actFun_isBergman g F.isBergman).vanish (actFun_isBergman g F.isBergman).finite
  map_add' F G := BergmanSpace.ext fun w => congrFun (actFun_add g F G) w
  map_smul' c F := BergmanSpace.ext fun w => congrFun (actFun_smul g c F) w

variable (k E) in
/-- The unitary representation of `GL₂(ℝ)` on the Bergman space. -/
def realRep : Representation ℂ (GL (Fin 2) ℝ) (BergmanSpace k E) where
  toFun := realOp k E
  map_one' := LinearMap.ext fun F =>
    BergmanSpace.ext fun w => actFun_one_apply F (fun _ hw => F.apply_eq_zero hw) w
  map_mul' g h := LinearMap.ext fun F => BergmanSpace.ext fun w => actFun_mul g h F w

theorem realRep_apply (g : GL (Fin 2) ℝ) (F : BergmanSpace k E) {w : ℂ} (hw : w.im ≠ 0) :
    realRep k E g F w = autFactor k g w • F (moeb g⁻¹ w) :=
  actFun_apply_of_im_ne_zero g F hw

theorem realRep_apply_of_im_eq_zero (g : GL (Fin 2) ℝ) (F : BergmanSpace k E) {w : ℂ}
    (hw : w.im = 0) : realRep k E g F w = 0 :=
  actFun_apply_of_im_eq_zero g F hw

theorem coe_realRep (g : GL (Fin 2) ℝ) (F : BergmanSpace k E) :
    ⇑(realRep k E g F) = actFun k g F :=
  rfl

end Real

section Finite

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (σ : Representation ℂ BinaryFiniteGL E)

/-- A norm-preserving linear map as a continuous linear map. -/
def finCLM (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (g : BinaryFiniteGL) : E →L[ℂ] E :=
  (σ g).mkContinuous 1 fun e => (hσ g e).le.trans_eq (one_mul _).symm

/-- The pointwise action `F ↦ σ g ∘ F`. -/
def finAct (g : BinaryFiniteGL) (F : ℂ → E) : ℂ → E :=
  fun w => σ g (F w)

theorem bergmanNormSq_finAct (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (g : BinaryFiniteGL) (F : ℂ → E) :
    bergmanNormSq k (finAct σ g F) = bergmanNormSq k F := by
  unfold bergmanNormSq finAct
  simp only [hσ]

theorem finAct_isBergman (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (g : BinaryFiniteGL) {F : ℂ → E}
    (hF : IsBergman k F) : IsBergman k (finAct σ g F) where
  holo := (finCLM σ hσ g).differentiable.comp_differentiableOn hF.holo
  vanish w hw := by simp [finAct, hF.vanish w hw]
  finite := by
    rw [bergmanNormSq_finAct σ hσ g F]
    exact hF.finite

variable (k) in
/-- The pointwise action of `σ g` on the Bergman space, as a linear map. -/
def finOp (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (g : BinaryFiniteGL) :
    BergmanSpace k E →ₗ[ℂ] BergmanSpace k E where
  toFun F := BergmanSpace.mk (finAct σ g F) (finAct_isBergman σ hσ g F.isBergman).holo
    (finAct_isBergman σ hσ g F.isBergman).vanish (finAct_isBergman σ hσ g F.isBergman).finite
  map_add' F G := BergmanSpace.ext fun w => (σ g).map_add (F w) (G w)
  map_smul' c F := BergmanSpace.ext fun w => (σ g).map_smul c (F w)

variable (k) in
/-- The unitary representation of `GL₂(𝔸_f)` on the Bergman space by `F ↦ σ g ∘ F`. -/
def finRep (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) : Representation ℂ BinaryFiniteGL (BergmanSpace k E) where
  toFun := finOp k σ hσ
  map_one' := LinearMap.ext fun F => BergmanSpace.ext fun w => by
    show σ 1 (F w) = F w
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun F => BergmanSpace.ext fun w => by
    show σ (g * h) (F w) = σ g (σ h (F w))
    rw [map_mul, Module.End.mul_apply]

theorem finRep_apply (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (u : BinaryFiniteGL) (F : BergmanSpace k E)
    (w : ℂ) : finRep k σ hσ u F w = σ u (F w) :=
  rfl

theorem coe_finRep (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (u : BinaryFiniteGL) (F : BergmanSpace k E) :
    ⇑(finRep k σ hσ u F) = finAct σ u F :=
  rfl

theorem realRep_finRep_comm (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (g : GL (Fin 2) ℝ) (u : BinaryFiniteGL)
    (F : BergmanSpace k E) :
    realRep k E g (finRep k σ hσ u F) = finRep k σ hσ u (realRep k E g F) := by
  refine BergmanSpace.ext fun w => ?_
  by_cases hw : w.im = 0
  · rw [realRep_apply_of_im_eq_zero g _ hw, finRep_apply, realRep_apply_of_im_eq_zero g _ hw,
      map_zero]
  · rw [realRep_apply g _ hw, finRep_apply, finRep_apply, realRep_apply g F hw, map_smul]

end Finite

section Hilbert

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_realRep (g : GL (Fin 2) ℝ) (F : BergmanSpace k E) : ‖realRep k E g F‖ = ‖F‖ := by
  have h2 : bergmanNormSq k ⇑(realRep k E g F) = bergmanNormSq k ⇑F :=
    bergmanNormSq_actFun g F.continuousOn
  have h : ‖realRep k E g F‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [BergmanSpace.norm_sq_eq, BergmanSpace.norm_sq_eq, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem inner_realRep (g : GL (Fin 2) ℝ) (F G : BergmanSpace k E) :
    inner ℂ (realRep k E g F) (realRep k E g G) = inner ℂ F G :=
  ({ toLinearMap := realRep k E g
     norm_map' := norm_realRep g } : BergmanSpace k E →ₗᵢ[ℂ] BergmanSpace k E).inner_map_map F G

theorem norm_finRep (σ : Representation ℂ BinaryFiniteGL E) (hσ : ∀ g e, ‖σ g e‖ = ‖e‖)
    (u : BinaryFiniteGL) (F : BergmanSpace k E) : ‖finRep k σ hσ u F‖ = ‖F‖ := by
  have h2 : bergmanNormSq k ⇑(finRep k σ hσ u F) = bergmanNormSq k ⇑F :=
    bergmanNormSq_finAct σ hσ u F
  have h : ‖finRep k σ hσ u F‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [BergmanSpace.norm_sq_eq, BergmanSpace.norm_sq_eq, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem coeffPlus_finRep [CompleteSpace E] (σ : Representation ℂ BinaryFiniteGL E)
    (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (u : BinaryFiniteGL) (F : BergmanSpace k E) (n : ℕ) :
    coeffPlus (finRep k σ hσ u F) n = σ u (coeffPlus F n) := by
  unfold coeffPlus
  exact upperCoeff_comp_clm (k := k) (finCLM σ hσ u) F.differentiableOn_upper.continuousOn n

theorem coeffMinus_finRep [CompleteSpace E] (σ : Representation ℂ BinaryFiniteGL E)
    (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (u : BinaryFiniteGL) (F : BergmanSpace k E) (n : ℕ) :
    coeffMinus (finRep k σ hσ u F) n = σ u (coeffMinus F n) := by
  unfold coeffMinus
  exact upperCoeff_comp_clm (k := k) (finCLM σ hσ u)
    F.differentiableOn_lowerPart.continuousOn n

end Hilbert

section Adelic

private theorem realPart_combineGL (r : BinaryRealGL) (f : BinaryFiniteGL) :
    SmoothVectors.realPart (combineGL r f) = r := by
  apply Units.ext
  ext i j
  rfl

private theorem finitePart_combineGL (r : BinaryRealGL) (f : BinaryFiniteGL) :
    SmoothVectors.finitePart (combineGL r f) = f := by
  apply Units.ext
  ext i j
  rfl

private theorem realPart_atInfinity (g : BinaryRealGL) :
    SmoothVectors.realPart (atInfinity g) = g :=
  realPart_combineGL g 1

private theorem finitePart_atInfinity (g : BinaryRealGL) :
    SmoothVectors.finitePart (atInfinity g) = 1 :=
  finitePart_combineGL g 1

private theorem realPart_atFinite (u : BinaryFiniteGL) :
    SmoothVectors.realPart (atFinite u) = 1 :=
  realPart_combineGL 1 u

private theorem finitePart_atFinite (u : BinaryFiniteGL) :
    SmoothVectors.finitePart (atFinite u) = u :=
  finitePart_combineGL 1 u

theorem mul_mul_swap_of_comm {A : Type*} [Monoid A] {a b c d : A} (h : b * c = c * b) :
    a * b * (c * d) = a * c * (b * d) :=
  calc a * b * (c * d) = a * (b * c) * d := by simp only [mul_assoc]
    _ = a * (c * b) * d := by rw [h]
    _ = a * c * (b * d) := by simp only [mul_assoc]

variable {k : ℕ}

/-- The unitary representation of `GL₂(𝔸)` on the Bergman space of a finite-adelic model:
`g ↦ realRep (g_∞) * finRep (g_f)`. -/
def bergmanRep (M : FiniteModel k) : Representation ℂ BinaryAdelicGL (BergmanSpace k M.E) where
  toFun x := realRep k M.E (SmoothVectors.realPart x) *
    finRep k M.σ M.unitary (SmoothVectors.finitePart x)
  map_one' := by simp only [map_one, mul_one]
  map_mul' x y := by
    simp only [map_mul]
    exact mul_mul_swap_of_comm
      (LinearMap.ext fun F => realRep_finRep_comm M.σ M.unitary _ _ F)

theorem bergmanRep_apply (M : FiniteModel k) (x : BinaryAdelicGL) (F : BergmanSpace k M.E) :
    bergmanRep M x F =
      realRep k M.E (SmoothVectors.realPart x)
        (finRep k M.σ M.unitary (SmoothVectors.finitePart x) F) :=
  rfl

theorem bergmanRep_eq (M : FiniteModel k) (x : BinaryAdelicGL) :
    bergmanRep M x =
      realRep k M.E (SmoothVectors.realPart x) *
        finRep k M.σ M.unitary (SmoothVectors.finitePart x) :=
  rfl

theorem bergmanRep_atInfinity (M : FiniteModel k) (g : BinaryRealGL) :
    bergmanRep M (atInfinity g) = realRep k M.E g := by
  rw [bergmanRep_eq, realPart_atInfinity, finitePart_atInfinity, map_one, mul_one]

theorem bergmanRep_atFinite (M : FiniteModel k) (u : BinaryFiniteGL) :
    bergmanRep M (atFinite u) = finRep k M.σ M.unitary u := by
  rw [bergmanRep_eq, realPart_atFinite, finitePart_atFinite, map_one, one_mul]

theorem bergmanRep_unitary (M : FiniteModel k) (x : BinaryAdelicGL) (F : BergmanSpace k M.E) :
    ‖bergmanRep M x F‖ = ‖F‖ := by
  rw [bergmanRep_apply, norm_realRep, norm_finRep]

instance (M : FiniteModel k) : AbstractIrreducibility.IsUnitary (bergmanRep M) :=
  ⟨bergmanRep_unitary M⟩

theorem bergmanRep_apply_fixed (M : FiniteModel k) {u : BinaryFiniteGL}
    {F : BergmanSpace k M.E} (h : bergmanRep M (atFinite u) F = F) (w : ℂ) :
    M.σ u (F w) = F w := by
  have h1 := DFunLike.congr_fun h w
  rw [bergmanRep_atFinite, finRep_apply] at h1
  exact h1

end Adelic

end TernaryPeriodPolynomials.Regularity

end
