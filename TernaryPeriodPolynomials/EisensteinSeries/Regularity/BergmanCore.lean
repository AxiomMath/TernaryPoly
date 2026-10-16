module

public import Mathlib
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Jacobian
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# The weighted Bergman space on `ℂ ∖ ℝ`

For a Hilbert space `E` and `k : ℕ`, `BergmanSpace k E` consists of the functions `F : ℂ → E`
that are holomorphic on `ℂ ∖ ℝ`, vanish on `ℝ`, and have finite norm
`‖F‖² = ∫ ‖F w‖² |Im w|^k dμ_hyp(w)`.  It is a type synonym for a submodule of `ℂ → E`, so that
the pointwise topology of `ℂ → E` is not inherited, and it carries the inner product
`⟪F, G⟫ = ∫ ⟪F w, G w⟫ |Im w|^k dμ_hyp(w)` built through `InnerProductSpace.Core`.

Definiteness uses that a function continuous on the open set `ℂ ∖ ℝ` which vanishes almost
everywhere vanishes identically.  Completeness (for `2 ≤ k`) and Parseval's identity are in
`Bergman.lean`.
-/

noncomputable section

open MeasureTheory

namespace TernaryPeriodPolynomials.Regularity

/-- `∫ ‖F w‖² |Im w|^k dμ_hyp`. -/
def bergmanNormSq {E : Type*} [NormedAddCommGroup E] (k : ℕ) (F : ℂ → E) : ENNReal :=
  ∫⁻ w, ENNReal.ofReal (‖F w‖ ^ 2 * |w.im| ^ k) ∂hypMeasure

namespace BergmanAux

theorem measurable_density : Measurable fun w : ℂ => ENNReal.ofReal ((w.im ^ 2)⁻¹) := by
  fun_prop

theorem hyp_ac : Measure.AbsolutelyContinuous hypMeasure (volume.restrict offReal) := by
  unfold hypMeasure
  exact withDensity_absolutelyContinuous _ _

theorem restrict_ac : Measure.AbsolutelyContinuous (volume.restrict offReal) hypMeasure := by
  unfold hypMeasure
  refine withDensity_absolutelyContinuous' measurable_density.aemeasurable ?_
  refine (ae_restrict_iff' measurableSet_offReal).2 (ae_of_all _ fun w hw => ?_)
  have hw' : w.im ≠ 0 := hw
  have hpos : 0 < w.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hw'))
  exact (ENNReal.ofReal_pos.2 (inv_pos.2 hpos)).ne'

theorem aesm {β : Type*} [NormedAddCommGroup β] {f : ℂ → β}
    (hf : ContinuousOn f offReal) : AEStronglyMeasurable f hypMeasure :=
  (hf.aestronglyMeasurable (μ := volume) measurableSet_offReal).mono_ac hyp_ac

theorem continuous_weight (k : ℕ) : Continuous fun w : ℂ => |w.im| ^ k :=
  (continuous_abs.comp Complex.continuous_im).pow k

theorem nonneg_weight {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) (k : ℕ) (w : ℂ) :
    0 ≤ ‖F w‖ ^ 2 * |w.im| ^ k := by positivity

theorem continuousOn_weight {E : Type*} [NormedAddCommGroup E] {k : ℕ} {F : ℂ → E} {s : Set ℂ}
    (hF : ContinuousOn F s) : ContinuousOn (fun w => ‖F w‖ ^ 2 * |w.im| ^ k) s :=
  (hF.norm.pow 2).mul (continuous_weight k).continuousOn

theorem normSq_ne_top_iff {E : Type*} [NormedAddCommGroup E] {k : ℕ} {F : ℂ → E}
    (hF : ContinuousOn F offReal) :
    bergmanNormSq k F ≠ ⊤ ↔ Integrable (fun w => ‖F w‖ ^ 2 * |w.im| ^ k) hypMeasure := by
  unfold bergmanNormSq
  exact lintegral_ofReal_ne_top_iff_integrable (aesm (continuousOn_weight hF))
    (ae_of_all _ fun w => nonneg_weight F k w)

theorem norm_add_sq_le {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg (a + b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

end BergmanAux

/-- The defining conditions of the Bergman space: holomorphic on `ℂ ∖ ℝ`, zero on `ℝ`, finite
Bergman norm. -/
structure IsBergman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k : ℕ) (F : ℂ → E) :
    Prop where
  holo : DifferentiableOn ℂ F offReal
  vanish : ∀ w : ℂ, w.im = 0 → F w = 0
  finite : bergmanNormSq k F ≠ ⊤

namespace IsBergman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ} {F G : ℂ → E}

theorem zero_mem : IsBergman k (0 : ℂ → E) where
  holo := differentiableOn_const 0
  vanish _ _ := rfl
  finite := by simp [bergmanNormSq]

theorem add (hF : IsBergman k F) (hG : IsBergman k G) : IsBergman k (F + G) where
  holo := hF.holo.add hG.holo
  vanish w hw := by simp [hF.vanish w hw, hG.vanish w hw]
  finite := by
    have hcont : ContinuousOn (F + G) offReal := (hF.holo.add hG.holo).continuousOn
    rw [BergmanAux.normSq_ne_top_iff hcont]
    have h1 := (BergmanAux.normSq_ne_top_iff hF.holo.continuousOn).1 hF.finite
    have h2 := (BergmanAux.normSq_ne_top_iff hG.holo.continuousOn).1 hG.finite
    have h3 : Integrable (fun w => 2 * (‖F w‖ ^ 2 * |w.im| ^ k + ‖G w‖ ^ 2 * |w.im| ^ k))
        hypMeasure := (h1.add h2).const_mul 2
    refine h3.mono' (BergmanAux.aesm (BergmanAux.continuousOn_weight hcont))
      (ae_of_all _ fun w => ?_)
    have hr : 0 ≤ |w.im| ^ k := by positivity
    show ‖‖(F + G) w‖ ^ 2 * |w.im| ^ k‖ ≤
      2 * (‖F w‖ ^ 2 * |w.im| ^ k + ‖G w‖ ^ 2 * |w.im| ^ k)
    rw [Real.norm_of_nonneg (BergmanAux.nonneg_weight (F + G) k w)]
    have hsq := BergmanAux.norm_add_sq_le (F w) (G w)
    calc ‖(F + G) w‖ ^ 2 * |w.im| ^ k ≤ 2 * (‖F w‖ ^ 2 + ‖G w‖ ^ 2) * |w.im| ^ k :=
          mul_le_mul_of_nonneg_right hsq hr
      _ = 2 * (‖F w‖ ^ 2 * |w.im| ^ k + ‖G w‖ ^ 2 * |w.im| ^ k) := by ring

theorem smul (c : ℂ) (hF : IsBergman k F) : IsBergman k (c • F) where
  holo := hF.holo.const_smul c
  vanish w hw := by simp [hF.vanish w hw]
  finite := by
    have hcont : ContinuousOn (c • F) offReal := (hF.holo.const_smul c).continuousOn
    rw [BergmanAux.normSq_ne_top_iff hcont]
    have h1 := (BergmanAux.normSq_ne_top_iff hF.holo.continuousOn).1 hF.finite
    refine (h1.const_mul (‖c‖ ^ 2)).congr (ae_of_all _ fun w => ?_)
    show ‖c‖ ^ 2 * (‖F w‖ ^ 2 * |w.im| ^ k) = ‖(c • F) w‖ ^ 2 * |w.im| ^ k
    rw [Pi.smul_apply, norm_smul, mul_pow]
    ring

end IsBergman

/-- Holomorphic on `ℂ ∖ ℝ`, zero on `ℝ`, finite Bergman norm. -/
def bergmanSubmodule (k : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ (ℂ → E) where
  carrier := {F | IsBergman k F}
  add_mem' {_ _} hF hG := IsBergman.add hF hG
  zero_mem' := IsBergman.zero_mem
  smul_mem' c _ hF := IsBergman.smul c hF

theorem mem_bergmanSubmodule {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} : F ∈ bergmanSubmodule k E ↔ IsBergman k F :=
  Iff.rfl

/-- The weighted Bergman space (a type synonym, so that the pointwise topology of `ℂ → E` is not
inherited). -/
def BergmanSpace (k : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Type _ :=
  bergmanSubmodule k E

namespace BergmanSpace

section Basic

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

instance : AddCommGroup (BergmanSpace k E) :=
  inferInstanceAs (AddCommGroup (bergmanSubmodule k E))

instance : Module ℂ (BergmanSpace k E) :=
  inferInstanceAs (Module ℂ (bergmanSubmodule k E))

instance : FunLike (BergmanSpace k E) ℂ E where
  coe F := (F : bergmanSubmodule k E).1
  coe_injective := fun _ _ h => Subtype.ext h

@[ext] theorem ext {F G : BergmanSpace k E} (h : ∀ w, F w = G w) : F = G :=
  DFunLike.ext _ _ h

@[simp] theorem coe_add (F G : BergmanSpace k E) : ⇑(F + G) = ⇑F + ⇑G := rfl

@[simp] theorem coe_smul (c : ℂ) (F : BergmanSpace k E) : ⇑(c • F) = c • ⇑F := rfl

@[simp] theorem coe_zero : ⇑(0 : BergmanSpace k E) = 0 := rfl

@[simp] theorem coe_neg (F : BergmanSpace k E) : ⇑(-F) = -⇑F := rfl

@[simp] theorem coe_sub (F G : BergmanSpace k E) : ⇑(F - G) = ⇑F - ⇑G := rfl

@[simp] theorem add_apply (F G : BergmanSpace k E) (w : ℂ) : (F + G) w = F w + G w := rfl

@[simp] theorem smul_apply (c : ℂ) (F : BergmanSpace k E) (w : ℂ) : (c • F) w = c • F w := rfl

@[simp] theorem zero_apply (w : ℂ) : (0 : BergmanSpace k E) w = 0 := rfl

@[simp] theorem neg_apply (F : BergmanSpace k E) (w : ℂ) : (-F) w = -F w := rfl

@[simp] theorem sub_apply (F G : BergmanSpace k E) (w : ℂ) : (F - G) w = F w - G w := rfl

theorem isBergman (F : BergmanSpace k E) : IsBergman k (F : ℂ → E) :=
  (F : bergmanSubmodule k E).2

/-- Build an element of the Bergman space from a function with the three defining properties. -/
def mk (F : ℂ → E) (holo : DifferentiableOn ℂ F offReal) (zero : ∀ w : ℂ, w.im = 0 → F w = 0)
    (finite : bergmanNormSq k F ≠ ⊤) : BergmanSpace k E :=
  (⟨F, (show IsBergman k F from ⟨holo, zero, finite⟩)⟩ : bergmanSubmodule k E)

@[simp] theorem coe_mk (F : ℂ → E) (holo : DifferentiableOn ℂ F offReal)
    (zero : ∀ w : ℂ, w.im = 0 → F w = 0) (finite : bergmanNormSq k F ≠ ⊤) :
    ⇑(mk F holo zero finite : BergmanSpace k E) = F :=
  rfl

theorem holo (F : BergmanSpace k E) : DifferentiableOn ℂ (F : ℂ → E) offReal :=
  F.isBergman.holo

theorem continuousOn (F : BergmanSpace k E) : ContinuousOn (F : ℂ → E) offReal :=
  F.holo.continuousOn

theorem apply_eq_zero (F : BergmanSpace k E) {w : ℂ} (hw : w.im = 0) : F w = 0 :=
  F.isBergman.vanish w hw

theorem bergmanNormSq_ne_top (F : BergmanSpace k E) : bergmanNormSq k (F : ℂ → E) ≠ ⊤ :=
  F.isBergman.finite

end Basic

section Inner

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem integrable_norm_sq (F : BergmanSpace k E) :
    Integrable (fun w => ‖F w‖ ^ 2 * |w.im| ^ k) hypMeasure :=
  (BergmanAux.normSq_ne_top_iff F.continuousOn).1 F.bergmanNormSq_ne_top

theorem integrable_inner (F G : BergmanSpace k E) :
    Integrable (fun w => inner ℂ (F w) (G w) * ((|w.im| ^ k : ℝ) : ℂ)) hypMeasure := by
  have h1 := integrable_norm_sq F
  have h2 := integrable_norm_sq G
  have h3 : Integrable (fun w => ‖F w‖ ^ 2 * |w.im| ^ k + ‖G w‖ ^ 2 * |w.im| ^ k) hypMeasure :=
    h1.add h2
  refine h3.mono' ?_ (ae_of_all _ fun w => ?_)
  · exact BergmanAux.aesm ((ContinuousOn.inner (𝕜 := ℂ) F.continuousOn G.continuousOn).mul
      (Complex.continuous_ofReal.comp (BergmanAux.continuous_weight k)).continuousOn)
  · have hr : 0 ≤ |w.im| ^ k := by positivity
    show ‖inner ℂ (F w) (G w) * ((|w.im| ^ k : ℝ) : ℂ)‖ ≤
      ‖F w‖ ^ 2 * |w.im| ^ k + ‖G w‖ ^ 2 * |w.im| ^ k
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    have h := norm_inner_le_norm (𝕜 := ℂ) (F w) (G w)
    have hab : ‖F w‖ * ‖G w‖ ≤ ‖F w‖ ^ 2 + ‖G w‖ ^ 2 := by
      nlinarith [sq_nonneg (‖F w‖ - ‖G w‖), norm_nonneg (F w), norm_nonneg (G w),
        mul_nonneg (norm_nonneg (F w)) (norm_nonneg (G w))]
    calc ‖inner ℂ (F w) (G w)‖ * |w.im| ^ k ≤ (‖F w‖ * ‖G w‖) * |w.im| ^ k :=
          mul_le_mul_of_nonneg_right h hr
      _ ≤ (‖F w‖ ^ 2 + ‖G w‖ ^ 2) * |w.im| ^ k := mul_le_mul_of_nonneg_right hab hr
      _ = ‖F w‖ ^ 2 * |w.im| ^ k + ‖G w‖ ^ 2 * |w.im| ^ k := by ring

/-- The pairing `∫ ⟪F w, G w⟫ |Im w|^k dμ_hyp`, before it is packaged as an inner product. -/
def bInner (F G : BergmanSpace k E) : ℂ :=
  ∫ w, inner ℂ (F w) (G w) * ((|w.im| ^ k : ℝ) : ℂ) ∂hypMeasure

theorem bInner_add_left (F G H : BergmanSpace k E) :
    bInner (F + G) H = bInner F H + bInner G H := by
  unfold bInner
  rw [← integral_add (integrable_inner F H) (integrable_inner G H)]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [BergmanSpace.add_apply, inner_add_left, add_mul]

theorem bInner_smul_left (F G : BergmanSpace k E) (c : ℂ) :
    bInner (c • F) G = (starRingEnd ℂ) c * bInner F G := by
  unfold bInner
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [BergmanSpace.smul_apply, inner_smul_left, mul_assoc]

theorem conj_bInner (F G : BergmanSpace k E) :
    (starRingEnd ℂ) (bInner G F) = bInner F G := by
  unfold bInner
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [map_mul, inner_conj_symm, Complex.conj_ofReal]

theorem re_inner_self_mul (x : E) (r : ℝ) : (inner ℂ x x * (r : ℂ)).re = ‖x‖ ^ 2 * r := by
  have h : (inner ℂ x x).re = ‖x‖ ^ 2 := by
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  rw [Complex.re_mul_ofReal, h]

theorem re_bInner_self (F : BergmanSpace k E) :
    (bInner F F).re = ∫ w, ‖F w‖ ^ 2 * |w.im| ^ k ∂hypMeasure := by
  have h := integral_re (integrable_inner F F)
  have h' : (bInner F F).re =
      ∫ w, (inner ℂ (F w) (F w) * ((|w.im| ^ k : ℝ) : ℂ)).re ∂hypMeasure := h.symm
  rw [h']
  exact integral_congr_ae (ae_of_all _ fun w => re_inner_self_mul (F w) _)

theorem eq_zero_of_integral_eq_zero (F : BergmanSpace k E)
    (h0 : ∫ w, ‖F w‖ ^ 2 * |w.im| ^ k ∂hypMeasure = 0) : F = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2 * |w.im| ^ k)
    (ae_of_all _ fun w => BergmanAux.nonneg_weight (F : ℂ → E) k w) (integrable_norm_sq F)).1 h0
  have h1 : ∀ᵐ w ∂(volume.restrict offReal), ‖F w‖ ^ 2 * |w.im| ^ k = 0 :=
    BergmanAux.restrict_ac.ae_eq hae
  have h2 : (F : ℂ → E) =ᵐ[volume.restrict offReal] fun _ => (0 : E) := by
    have h3 := (ae_restrict_iff' measurableSet_offReal).1 h1
    refine (ae_restrict_iff' measurableSet_offReal).2 ?_
    filter_upwards [h3] with w hw hwm
    have hwm' : w.im ≠ 0 := hwm
    have hk : |w.im| ^ k ≠ 0 := pow_ne_zero _ (abs_ne_zero.2 hwm')
    have h4 : ‖F w‖ ^ 2 * |w.im| ^ k = 0 := hw hwm
    have h5 : ‖F w‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact h
      · exact absurd h hk
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h5)
  have heq := Measure.eqOn_open_of_ae_eq h2 isOpen_offReal F.continuousOn continuousOn_const
  refine BergmanSpace.ext fun w => ?_
  show F w = 0
  by_cases hw : w.im = 0
  · exact F.apply_eq_zero hw
  · exact heq (show w ∈ offReal from hw)

@[instance_reducible] def bergmanCore : InnerProductSpace.Core ℂ (BergmanSpace k E) where
  inner := bInner
  conj_inner_symm := conj_bInner
  re_inner_nonneg F := by
    have h : 0 ≤ (bInner F F).re := by
      rw [re_bInner_self]
      exact integral_nonneg fun w => BergmanAux.nonneg_weight (F : ℂ → E) k w
    exact h
  add_left := bInner_add_left
  smul_left := bInner_smul_left
  definite F h := by
    have h' : bInner F F = 0 := h
    have h0 : ∫ w, ‖F w‖ ^ 2 * |w.im| ^ k ∂hypMeasure = 0 := by
      have := re_bInner_self F
      rw [h'] at this
      simpa using this.symm
    exact eq_zero_of_integral_eq_zero F h0

instance : NormedAddCommGroup (BergmanSpace k E) := by
  letI : InnerProductSpace.Core ℂ (BergmanSpace k E) := bergmanCore (k := k) (E := E)
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (BergmanSpace k E) := by
  letI : InnerProductSpace.Core ℂ (BergmanSpace k E) := bergmanCore (k := k) (E := E)
  exact InnerProductSpace.ofCore (bergmanCore (k := k) (E := E)).toCore

theorem inner_def (F G : BergmanSpace k E) :
    inner ℂ F G = ∫ w, inner ℂ (F w) (G w) * ((|w.im| ^ k : ℝ) : ℂ) ∂hypMeasure :=
  rfl

theorem norm_sq_eq_integral (F : BergmanSpace k E) :
    ‖F‖ ^ 2 = ∫ w, ‖F w‖ ^ 2 * |w.im| ^ k ∂hypMeasure := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) F]
  exact re_bInner_self F

theorem norm_sq_eq (F : BergmanSpace k E) :
    ‖F‖ ^ 2 = (bergmanNormSq k (F : ℂ → E)).toReal := by
  rw [norm_sq_eq_integral, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun w => BergmanAux.nonneg_weight (F : ℂ → E) k w)
    (integrable_norm_sq F).aestronglyMeasurable]
  rfl

end Inner

end BergmanSpace

end TernaryPeriodPolynomials.Regularity

end
