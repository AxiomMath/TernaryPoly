module

public import Mathlib
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.BergmanCore
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.UpperHalf

@[expose] public section


/-!
# Parseval and completeness of the Bergman space

For `2 ≤ k` an element `F` of `BergmanSpace k E` has two families of coefficients: `coeffPlus F n`
is the `n`-th coefficient of `F` on the upper half plane and `coeffMinus F n` that of the
reflection `z ↦ F (-z)` of its restriction to the lower half plane.  Parseval's identity on the
upper half plane gives
`‖F‖² = ∑ₙ 4^(1-k) βₙ (‖coeffPlus F n‖² + ‖coeffMinus F n‖²)`
with `βₙ = discMoment (2 n) (k - 2)`.  Equivalently `F ↦ (√(4^(1-k) βₙ) • coefficient)` is a
linear isometry `bergmanToLp` into `ℓ²(ℕ ⊕ ℕ; E)`.  It is onto, since any square summable family
of scaled coefficients comes from an element `ofCoeff`; this gives completeness, the polarized
Parseval identity and continuity of the coefficient functionals.  The lowest weight vectors
`lowestMinus`, `lowestPlus` (supported on a single half plane, with coefficient sequence a point
mass at `0`) are also constructed.
-/

noncomputable section

open MeasureTheory

namespace TernaryPeriodPolynomials.Regularity

/-! ### Generic facts -/

namespace BergmanAux

theorem memℓp_two_of_summable {ι G : Type*} [NormedAddCommGroup G] {f : ι → G}
    (hf : Summable fun i => ‖f i‖ ^ 2) : Memℓp (E := fun _ : ι => G) f 2 := by
  refine memℓp_gen ?_
  simpa using hf

theorem lp_hasSum_norm_sq {ι G : Type*} [NormedAddCommGroup G] (f : lp (fun _ : ι => G) 2) :
    HasSum (fun i => ‖f i‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) f
  simpa using h

theorem hasSum_inl_add_inr {M : Type*} [NormedAddCommGroup M] [CompleteSpace M]
    {f : ℕ ⊕ ℕ → M} {a : M} (h : HasSum f a) :
    HasSum (fun n => f (Sum.inl n) + f (Sum.inr n)) a := by
  have hl : Summable (f ∘ Sum.inl) := h.summable.comp_injective Sum.inl_injective
  have hr : Summable (f ∘ Sum.inr) := h.summable.comp_injective Sum.inr_injective
  have h2 := HasSum.sum hl.hasSum hr.hasSum
  rw [h.unique h2]
  exact hl.hasSum.add hr.hasSum

theorem discMoment_pos_k {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    0 < discMoment (2 * n) ((k : ℝ) - 2) := by
  have ha : (-1 : ℝ) < (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact discMoment_pos _ ha

theorem four_rpow_pos (k : ℕ) : 0 < (4 : ℝ) ^ (1 - (k : ℝ)) :=
  Real.rpow_pos_of_pos (by norm_num) _

section Group

variable {E : Type*} [NormedAddCommGroup E]

theorem summable_zeroSeq (k : ℕ) :
    Summable fun n : ℕ => ‖(0 : E)‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2) := by
  simp

end Group

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_sq_scale_smul (s : ℝ) (hs : 0 ≤ s) (x : E) :
    ‖(s : ℂ) • x‖ ^ 2 = s ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs, mul_pow]

theorem norm_sq_inv_smul (s : ℝ) (hs : 0 < s) (x : E) :
    ‖((s⁻¹ : ℝ) : ℂ) • x‖ ^ 2 = (s ^ 2)⁻¹ * ‖x‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs.le), mul_pow, inv_pow]

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_scale_smul (s : ℝ) (x y : E) :
    inner ℂ ((s : ℂ) • x) ((s : ℂ) • y) = ((s ^ 2 : ℝ) : ℂ) * inner ℂ x y := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc]
  push_cast
  ring

end Inner

end BergmanAux

/-! ### The weights -/

/-- The weight `4^(1-k) βₙ` of the `n`-th coefficient in Parseval's identity, where
`βₙ = ∫_{|ζ|<1} |ζ|^(2n) (1 - |ζ|²)^(k-2)`. -/
def bergmanWeight (k n : ℕ) : ℝ := (4 : ℝ) ^ (1 - (k : ℝ)) * discMoment (2 * n) ((k : ℝ) - 2)

/-- The square root of `bergmanWeight`, the scaling of the `n`-th coefficient. -/
def bergmanScale (k n : ℕ) : ℝ := Real.sqrt (bergmanWeight k n)

section Weights

variable {k : ℕ}

theorem bergmanWeight_pos (hk : 2 ≤ k) (n : ℕ) : 0 < bergmanWeight k n :=
  mul_pos (BergmanAux.four_rpow_pos k) (BergmanAux.discMoment_pos_k hk n)

theorem bergmanScale_nonneg (k n : ℕ) : 0 ≤ bergmanScale k n := Real.sqrt_nonneg _

theorem bergmanScale_pos (hk : 2 ≤ k) (n : ℕ) : 0 < bergmanScale k n :=
  Real.sqrt_pos.2 (bergmanWeight_pos hk n)

theorem bergmanScale_sq (hk : 2 ≤ k) (n : ℕ) : bergmanScale k n ^ 2 = bergmanWeight k n :=
  Real.sq_sqrt (bergmanWeight_pos hk n).le

end Weights

section Coefficients

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The `n`-th coefficient of `F` on the upper half plane. -/
def coeffPlus (F : BergmanSpace k E) (n : ℕ) : E := upperCoeff k (F : ℂ → E) n

/-- The `n`-th coefficient of the reflection `z ↦ F (-z)` of `F` restricted to the lower half
plane. -/
def coeffMinus (F : BergmanSpace k E) (n : ℕ) : E := upperCoeff k (lowerPart (F : ℂ → E)) n

namespace BergmanSpace

theorem differentiableOn_upper (F : BergmanSpace k E) :
    DifferentiableOn ℂ (F : ℂ → E) upper :=
  F.holo.mono upper_subset_offReal

theorem differentiableOn_lowerPart (F : BergmanSpace k E) :
    DifferentiableOn ℂ (lowerPart (F : ℂ → E)) upper := by
  have hneg : DifferentiableOn ℂ (fun z : ℂ => -z) upper := differentiableOn_id.neg
  have hmaps : Set.MapsTo (fun z : ℂ => -z) upper offReal := by
    intro z hz
    have hz' : 0 < z.im := hz
    show (-z).im ≠ 0
    rw [Complex.neg_im]
    exact neg_ne_zero.2 hz'.ne'
  exact F.holo.comp hneg hmaps

end BergmanSpace

theorem coeffPlus_add [CompleteSpace E] (F G : BergmanSpace k E) (n : ℕ) :
    coeffPlus (F + G) n = coeffPlus F n + coeffPlus G n := by
  unfold coeffPlus
  rw [show (⇑(F + G) : ℂ → E) = fun z => F z + G z from rfl]
  exact upperCoeff_add F.differentiableOn_upper.continuousOn G.differentiableOn_upper.continuousOn n

theorem coeffPlus_smul [CompleteSpace E] (c : ℂ) (F : BergmanSpace k E) (n : ℕ) :
    coeffPlus (c • F) n = c • coeffPlus F n := by
  unfold coeffPlus
  rw [show (⇑(c • F) : ℂ → E) = fun z => c • F z from rfl]
  exact upperCoeff_smul c n

theorem coeffMinus_add [CompleteSpace E] (F G : BergmanSpace k E) (n : ℕ) :
    coeffMinus (F + G) n = coeffMinus F n + coeffMinus G n := by
  unfold coeffMinus
  rw [show lowerPart (⇑(F + G) : ℂ → E) =
    fun z => lowerPart (F : ℂ → E) z + lowerPart (G : ℂ → E) z from rfl]
  exact upperCoeff_add F.differentiableOn_lowerPart.continuousOn
    G.differentiableOn_lowerPart.continuousOn n

theorem coeffMinus_smul [CompleteSpace E] (c : ℂ) (F : BergmanSpace k E) (n : ℕ) :
    coeffMinus (c • F) n = c • coeffMinus F n := by
  unfold coeffMinus
  rw [show lowerPart (⇑(c • F) : ℂ → E) = fun z => c • lowerPart (F : ℂ → E) z from rfl]
  exact upperCoeff_smul c n

end Coefficients

section Parseval

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Parseval's identity for the hyperbolic `L²` norm of a function that is holomorphic on both
half planes: the norm is the sum of the weighted squared coefficients of the two halves. -/
theorem bergmanNormSq_eq_tsum [CompleteSpace E] (hk : 2 ≤ k) {F : ℂ → E}
    (hp : DifferentiableOn ℂ F upper) (hm : DifferentiableOn ℂ (lowerPart F) upper) :
    bergmanNormSq k F =
      (∑' n, ENNReal.ofReal (bergmanWeight k n * ‖upperCoeff k F n‖ ^ 2)) +
        ∑' n, ENNReal.ofReal (bergmanWeight k n * ‖upperCoeff k (lowerPart F) n‖ ^ 2) := by
  have hweight : ∀ G : ℂ → E,
      (∑' n, ENNReal.ofReal ((4 : ℝ) ^ (1 - (k : ℝ)) *
        (‖upperCoeff k G n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)))) =
      ∑' n, ENNReal.ofReal (bergmanWeight k n * ‖upperCoeff k G n‖ ^ 2) := by
    intro G
    refine tsum_congr fun n => ?_
    congr 1
    unfold bergmanWeight
    ring
  have hsplit := lintegral_hypMeasure_split (fun w => ENNReal.ofReal (‖F w‖ ^ 2 * |w.im| ^ k))
  have h1 : ∫⁻ z in upper, ENNReal.ofReal (‖F z‖ ^ 2 * |z.im| ^ k) ∂hypMeasure =
      ∑' n, ENNReal.ofReal (bergmanWeight k n * ‖upperCoeff k F n‖ ^ 2) := by
    refine Eq.trans ?_ ((lintegral_upper_norm_sq hk hp).trans (hweight F))
    refine setLIntegral_congr_fun measurableSet_upper (fun z hz => ?_)
    have hz' : 0 < z.im := hz
    show ENNReal.ofReal (‖F z‖ ^ 2 * |z.im| ^ k) = ENNReal.ofReal (‖F z‖ ^ 2 * z.im ^ k)
    rw [abs_of_pos hz']
  have h2 : ∫⁻ z in upper, ENNReal.ofReal (‖F (-z)‖ ^ 2 * |(-z).im| ^ k) ∂hypMeasure =
      ∑' n, ENNReal.ofReal (bergmanWeight k n * ‖upperCoeff k (lowerPart F) n‖ ^ 2) := by
    refine Eq.trans ?_ ((lintegral_upper_norm_sq hk hm).trans (hweight (lowerPart F)))
    refine setLIntegral_congr_fun measurableSet_upper (fun z hz => ?_)
    have hz' : 0 < z.im := hz
    show ENNReal.ofReal (‖F (-z)‖ ^ 2 * |(-z).im| ^ k) =
      ENNReal.ofReal (‖lowerPart F z‖ ^ 2 * z.im ^ k)
    rw [Complex.neg_im, abs_neg, abs_of_pos hz']
    try rfl
  unfold bergmanNormSq
  rw [hsplit, h1, h2]

theorem bergmanNormSq_eq [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) :
    bergmanNormSq k (F : ℂ → E) =
      (∑' n, ENNReal.ofReal (bergmanWeight k n * ‖coeffPlus F n‖ ^ 2)) +
        ∑' n, ENNReal.ofReal (bergmanWeight k n * ‖coeffMinus F n‖ ^ 2) :=
  bergmanNormSq_eq_tsum hk F.differentiableOn_upper F.differentiableOn_lowerPart

theorem exists_hasSum_parts [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) :
    ∃ a b : ℝ, HasSum (fun n => bergmanWeight k n * ‖coeffPlus F n‖ ^ 2) a ∧
      HasSum (fun n => bergmanWeight k n * ‖coeffMinus F n‖ ^ 2) b ∧ ‖F‖ ^ 2 = a + b := by
  have hfin := F.bergmanNormSq_ne_top
  rw [bergmanNormSq_eq hk F] at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_ne_top.1 hfin
  have hA : ∀ n, 0 ≤ bergmanWeight k n * ‖coeffPlus F n‖ ^ 2 := fun n =>
    mul_nonneg (bergmanWeight_pos hk n).le (sq_nonneg _)
  have hB : ∀ n, 0 ≤ bergmanWeight k n * ‖coeffMinus F n‖ ^ 2 := fun n =>
    mul_nonneg (bergmanWeight_pos hk n).le (sq_nonneg _)
  have sA : Summable fun n => bergmanWeight k n * ‖coeffPlus F n‖ ^ 2 :=
    (ENNReal.summable_toReal h1).congr fun n => ENNReal.toReal_ofReal (hA n)
  have sB : Summable fun n => bergmanWeight k n * ‖coeffMinus F n‖ ^ 2 :=
    (ENNReal.summable_toReal h2).congr fun n => ENNReal.toReal_ofReal (hB n)
  refine ⟨_, _, sA.hasSum, sB.hasSum, ?_⟩
  rw [BergmanSpace.norm_sq_eq F, bergmanNormSq_eq hk F,
    ← ENNReal.ofReal_tsum_of_nonneg hA sA, ← ENNReal.ofReal_tsum_of_nonneg hB sB,
    ← ENNReal.ofReal_add (tsum_nonneg hA) (tsum_nonneg hB),
    ENNReal.toReal_ofReal (add_nonneg (tsum_nonneg hA) (tsum_nonneg hB))]

/-- **Parseval** for the Bergman space. -/
theorem hasSum_norm_sq [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) :
    HasSum (fun n => (4 : ℝ) ^ (1 - (k : ℝ)) * discMoment (2 * n) ((k : ℝ) - 2) *
      (‖coeffPlus F n‖ ^ 2 + ‖coeffMinus F n‖ ^ 2)) (‖F‖ ^ 2) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_hasSum_parts hk F
  have hfun : (fun n => (4 : ℝ) ^ (1 - (k : ℝ)) * discMoment (2 * n) ((k : ℝ) - 2) *
      (‖coeffPlus F n‖ ^ 2 + ‖coeffMinus F n‖ ^ 2)) =
      fun n => bergmanWeight k n * ‖coeffPlus F n‖ ^ 2 +
        bergmanWeight k n * ‖coeffMinus F n‖ ^ 2 := by
    funext n
    unfold bergmanWeight
    ring
  rw [hfun, hab]
  exact ha.add hb

end Parseval

section Isometry

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The coefficients of `F`, each scaled by `√(4^(1-k) βₙ)`, indexed by `ℕ ⊕ ℕ`. -/
def scaledCoeff (F : BergmanSpace k E) : ℕ ⊕ ℕ → E :=
  Sum.elim (fun n => ((bergmanScale k n : ℝ) : ℂ) • coeffPlus F n)
    (fun n => ((bergmanScale k n : ℝ) : ℂ) • coeffMinus F n)

theorem norm_sq_scaledCoeff_inl (hk : 2 ≤ k) (F : BergmanSpace k E) (n : ℕ) :
    ‖scaledCoeff F (Sum.inl n)‖ ^ 2 = bergmanWeight k n * ‖coeffPlus F n‖ ^ 2 := by
  show ‖((bergmanScale k n : ℝ) : ℂ) • coeffPlus F n‖ ^ 2 = _
  rw [BergmanAux.norm_sq_scale_smul _ (bergmanScale_nonneg k n), bergmanScale_sq hk]

theorem norm_sq_scaledCoeff_inr (hk : 2 ≤ k) (F : BergmanSpace k E) (n : ℕ) :
    ‖scaledCoeff F (Sum.inr n)‖ ^ 2 = bergmanWeight k n * ‖coeffMinus F n‖ ^ 2 := by
  show ‖((bergmanScale k n : ℝ) : ℂ) • coeffMinus F n‖ ^ 2 = _
  rw [BergmanAux.norm_sq_scale_smul _ (bergmanScale_nonneg k n), bergmanScale_sq hk]

theorem hasSum_scaledCoeff [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) :
    HasSum (fun i => ‖scaledCoeff F i‖ ^ 2) (‖F‖ ^ 2) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_hasSum_parts hk F
  rw [hab]
  have hl : HasSum (fun n => ‖scaledCoeff F (Sum.inl n)‖ ^ 2) a := by
    simp only [norm_sq_scaledCoeff_inl hk]
    exact ha
  have hr : HasSum (fun n => ‖scaledCoeff F (Sum.inr n)‖ ^ 2) b := by
    simp only [norm_sq_scaledCoeff_inr hk]
    exact hb
  exact HasSum.sum (f := fun i => ‖scaledCoeff F i‖ ^ 2) hl hr

/-- The scaled coefficients of `F` as an element of `ℓ²(ℕ ⊕ ℕ; E)`. -/
def bergmanToLpFun [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) :
    lp (fun _ : ℕ ⊕ ℕ => E) 2 :=
  ⟨scaledCoeff F, BergmanAux.memℓp_two_of_summable (hasSum_scaledCoeff hk F).summable⟩

theorem bergmanToLpFun_add [CompleteSpace E] (hk : 2 ≤ k) (F G : BergmanSpace k E) :
    bergmanToLpFun hk (F + G) = bergmanToLpFun hk F + bergmanToLpFun hk G := by
  refine lp.ext (funext fun i => ?_)
  rcases i with n | n
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffPlus (F + G) n =
      ((bergmanScale k n : ℝ) : ℂ) • coeffPlus F n +
        ((bergmanScale k n : ℝ) : ℂ) • coeffPlus G n
    rw [coeffPlus_add, smul_add]
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffMinus (F + G) n =
      ((bergmanScale k n : ℝ) : ℂ) • coeffMinus F n +
        ((bergmanScale k n : ℝ) : ℂ) • coeffMinus G n
    rw [coeffMinus_add, smul_add]

theorem bergmanToLpFun_smul [CompleteSpace E] (hk : 2 ≤ k) (c : ℂ) (F : BergmanSpace k E) :
    bergmanToLpFun hk (c • F) = c • bergmanToLpFun hk F := by
  refine lp.ext (funext fun i => ?_)
  rcases i with n | n
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffPlus (c • F) n =
      c • (((bergmanScale k n : ℝ) : ℂ) • coeffPlus F n)
    rw [coeffPlus_smul]
    exact smul_comm _ _ _
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffMinus (c • F) n =
      c • (((bergmanScale k n : ℝ) : ℂ) • coeffMinus F n)
    rw [coeffMinus_smul]
    exact smul_comm _ _ _

theorem norm_bergmanToLpFun [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) :
    ‖bergmanToLpFun hk F‖ = ‖F‖ := by
  have h := BergmanAux.lp_hasSum_norm_sq (bergmanToLpFun hk F)
  have h' := hasSum_scaledCoeff hk F
  have heq : ‖bergmanToLpFun hk F‖ ^ 2 = ‖F‖ ^ 2 := h.unique h'
  calc ‖bergmanToLpFun hk F‖ = Real.sqrt (‖bergmanToLpFun hk F‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖F‖ ^ 2) := by rw [heq]
    _ = ‖F‖ := Real.sqrt_sq (norm_nonneg _)

/-- The linear isometry `F ↦ (√(4^(1-k) βₙ) • coefficient)` from the Bergman space to
`ℓ²(ℕ ⊕ ℕ; E)`. -/
def bergmanToLp [CompleteSpace E] (hk : 2 ≤ k) :
    BergmanSpace k E →ₗᵢ[ℂ] lp (fun _ : ℕ ⊕ ℕ => E) 2 where
  toFun := bergmanToLpFun hk
  map_add' := bergmanToLpFun_add hk
  map_smul' c F := bergmanToLpFun_smul hk c F
  norm_map' := norm_bergmanToLpFun hk

end Isometry

section OfCoeff

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The function equal to `upperSeries k c` on the upper half plane, to `w ↦ upperSeries k d (-w)`
on the lower half plane and to `0` on the real axis. -/
def ofCoeffFun (k : ℕ) (c d : ℕ → E) (w : ℂ) : E :=
  if 0 < w.im then upperSeries k c w else if w.im < 0 then upperSeries k d (-w) else 0

theorem ofCoeffFun_of_pos {c d : ℕ → E} {w : ℂ} (h : 0 < w.im) :
    ofCoeffFun k c d w = upperSeries k c w := by
  unfold ofCoeffFun
  rw [ite_eq_left h]

theorem ofCoeffFun_of_neg {c d : ℕ → E} {w : ℂ} (h : w.im < 0) :
    ofCoeffFun k c d w = upperSeries k d (-w) := by
  unfold ofCoeffFun
  rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h]

theorem ofCoeffFun_of_eq {c d : ℕ → E} {w : ℂ} (h : w.im = 0) :
    ofCoeffFun k c d w = 0 := by
  unfold ofCoeffFun
  rw [ite_eq_right (not_lt.2 h.le), ite_eq_right (not_lt.2 h.ge)]

theorem differentiableOn_upperSeries_of_summable [CompleteSpace E] (hk : 2 ≤ k) {c : ℕ → E}
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) :
    DifferentiableOn ℂ (upperSeries k c) upper := by
  obtain ⟨C, hC⟩ := exists_bound_of_summable hk hc
  exact differentiableOn_upperSeries hC

theorem differentiableOn_ofCoeffFun [CompleteSpace E] (hk : 2 ≤ k) {c d : ℕ → E}
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2))
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) :
    DifferentiableOn ℂ (ofCoeffFun k c d) offReal := by
  intro w hw
  have hw' : w.im ≠ 0 := hw
  rcases lt_or_gt_of_ne hw' with hneg | hpos
  · have hopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
    have hmaps : Set.MapsTo (fun z : ℂ => -z) {z : ℂ | z.im < 0} upper := by
      intro z hz
      have hz' : z.im < 0 := hz
      show 0 < (-z).im
      rw [Complex.neg_im]
      linarith
    have hneg' : DifferentiableOn ℂ (fun z : ℂ => -z) {z : ℂ | z.im < 0} :=
      differentiableOn_id.neg
    have hd' : DifferentiableOn ℂ (fun z => upperSeries k d (-z)) {z : ℂ | z.im < 0} :=
      (differentiableOn_upperSeries_of_summable hk hd).comp hneg' hmaps
    have hat : DifferentiableAt ℂ (fun z => upperSeries k d (-z)) w :=
      hd'.differentiableAt (hopen.mem_nhds hneg)
    have hev : Filter.EventuallyEq (nhds w) (ofCoeffFun k c d)
        (fun z => upperSeries k d (-z)) :=
      Filter.eventually_of_mem (hopen.mem_nhds hneg) (fun z hz => ofCoeffFun_of_neg hz)
    exact (hat.congr_of_eventuallyEq hev).differentiableWithinAt
  · have hopen : IsOpen upper := isOpen_upper
    have hup : w ∈ upper := hpos
    have hat : DifferentiableAt ℂ (upperSeries k c) w :=
      (differentiableOn_upperSeries_of_summable hk hc).differentiableAt (hopen.mem_nhds hup)
    have hev : Filter.EventuallyEq (nhds w) (ofCoeffFun k c d) (upperSeries k c) :=
      Filter.eventually_of_mem (hopen.mem_nhds hup)
        (fun z hz => ofCoeffFun_of_pos (mem_upper_iff.1 hz))
    exact (hat.congr_of_eventuallyEq hev).differentiableWithinAt

theorem lowerPart_ofCoeffFun {c d : ℕ → E} {z : ℂ} (hz : z ∈ upper) :
    lowerPart (ofCoeffFun k c d) z = upperSeries k d z := by
  have hz' : 0 < z.im := hz
  have hn : (-z).im < 0 := by
    rw [Complex.neg_im]
    linarith
  show ofCoeffFun k c d (-z) = _
  rw [ofCoeffFun_of_neg hn, neg_neg]

theorem differentiableOn_lowerPart_ofCoeffFun [CompleteSpace E] (hk : 2 ≤ k) {c d : ℕ → E}
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) :
    DifferentiableOn ℂ (lowerPart (ofCoeffFun k c d)) upper :=
  (differentiableOn_upperSeries_of_summable hk hd).congr fun _ hz => lowerPart_ofCoeffFun hz

theorem upperCoeff_ofCoeffFun [CompleteSpace E] (hk : 2 ≤ k) {c d : ℕ → E}
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) (n : ℕ) :
    upperCoeff k (ofCoeffFun k c d) n = c n := by
  obtain ⟨C, hC⟩ := exists_bound_of_summable hk hc
  exact (upperCoeff_congr (G := ofCoeffFun k c d) (G' := upperSeries k c)
    (fun z hz => ofCoeffFun_of_pos (mem_upper_iff.1 hz)) n).trans (upperCoeff_upperSeries hC n)

theorem upperCoeff_lowerPart_ofCoeffFun [CompleteSpace E] (hk : 2 ≤ k) {c d : ℕ → E}
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) (n : ℕ) :
    upperCoeff k (lowerPart (ofCoeffFun k c d)) n = d n := by
  obtain ⟨C, hC⟩ := exists_bound_of_summable hk hd
  exact (upperCoeff_congr (G := lowerPart (ofCoeffFun k c d)) (G' := upperSeries k d)
    (fun z hz => lowerPart_ofCoeffFun hz) n).trans (upperCoeff_upperSeries hC n)

theorem bergmanNormSq_ofCoeffFun_ne_top [CompleteSpace E] (hk : 2 ≤ k) {c d : ℕ → E}
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2))
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) :
    bergmanNormSq k (ofCoeffFun k c d) ≠ ⊤ := by
  rw [bergmanNormSq_eq_tsum hk
    ((differentiableOn_ofCoeffFun hk hc hd).mono upper_subset_offReal)
    (differentiableOn_lowerPart_ofCoeffFun hk hd)]
  simp only [upperCoeff_ofCoeffFun hk hc, upperCoeff_lowerPart_ofCoeffFun hk hd]
  have hA : ∀ n, 0 ≤ bergmanWeight k n * ‖c n‖ ^ 2 := fun n =>
    mul_nonneg (bergmanWeight_pos hk n).le (sq_nonneg _)
  have hB : ∀ n, 0 ≤ bergmanWeight k n * ‖d n‖ ^ 2 := fun n =>
    mul_nonneg (bergmanWeight_pos hk n).le (sq_nonneg _)
  have sA : Summable fun n => bergmanWeight k n * ‖c n‖ ^ 2 :=
    (hc.mul_left ((4 : ℝ) ^ (1 - (k : ℝ)))).congr fun n => by
      show (4 : ℝ) ^ (1 - (k : ℝ)) * (‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) =
        bergmanWeight k n * ‖c n‖ ^ 2
      unfold bergmanWeight
      ring
  have sB : Summable fun n => bergmanWeight k n * ‖d n‖ ^ 2 :=
    (hd.mul_left ((4 : ℝ) ^ (1 - (k : ℝ)))).congr fun n => by
      show (4 : ℝ) ^ (1 - (k : ℝ)) * (‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) =
        bergmanWeight k n * ‖d n‖ ^ 2
      unfold bergmanWeight
      ring
  rw [← ENNReal.ofReal_tsum_of_nonneg hA sA, ← ENNReal.ofReal_tsum_of_nonneg hB sB]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩

/-- The element of the Bergman space with upper coefficients `c` and lower coefficients `d`; its
function is `upperSeries k c` on the upper half plane, `w ↦ upperSeries k d (-w)` on the lower
half plane and `0` on the real axis. -/
def ofCoeff [CompleteSpace E] (hk : 2 ≤ k) (c d : ℕ → E)
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2))
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) :
    BergmanSpace k E :=
  BergmanSpace.mk (ofCoeffFun k c d) (differentiableOn_ofCoeffFun hk hc hd)
    (fun _ hw => ofCoeffFun_of_eq hw) (bergmanNormSq_ofCoeffFun_ne_top hk hc hd)

theorem coe_ofCoeff [CompleteSpace E] (hk : 2 ≤ k) (c d : ℕ → E)
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2))
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) :
    ⇑(ofCoeff hk c d hc hd) = ofCoeffFun k c d :=
  rfl

theorem coeffPlus_ofCoeff [CompleteSpace E] (hk : 2 ≤ k) (c d : ℕ → E)
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2))
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) (n : ℕ) :
    coeffPlus (ofCoeff hk c d hc hd) n = c n :=
  upperCoeff_ofCoeffFun hk hc n

theorem coeffMinus_ofCoeff [CompleteSpace E] (hk : 2 ≤ k) (c d : ℕ → E)
    (hc : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2))
    (hd : Summable fun n => ‖d n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) (n : ℕ) :
    coeffMinus (ofCoeff hk c d hc hd) n = d n :=
  upperCoeff_lowerPart_ofCoeffFun hk hd n

end OfCoeff

section Hilbert

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The coefficients `x n` multiplied by `1 / √(4^(1-k) βₙ)`. -/
def bergmanUnscale (k : ℕ) (x : ℕ → E) (n : ℕ) : E := (((bergmanScale k n)⁻¹ : ℝ) : ℂ) • x n

theorem summable_bergmanUnscale (hk : 2 ≤ k) (x : ℕ → E) (hx : Summable fun n => ‖x n‖ ^ 2) :
    Summable fun n => ‖bergmanUnscale k x n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2) := by
  refine (hx.mul_left (((4 : ℝ) ^ (1 - (k : ℝ)))⁻¹)).congr fun n => ?_
  have hβ : discMoment (2 * n) ((k : ℝ) - 2) ≠ 0 := (BergmanAux.discMoment_pos_k hk n).ne'
  unfold bergmanUnscale
  rw [BergmanAux.norm_sq_inv_smul _ (bergmanScale_pos hk n), bergmanScale_sq hk n]
  unfold bergmanWeight
  calc ((4 : ℝ) ^ (1 - (k : ℝ)))⁻¹ * ‖x n‖ ^ 2
      = ((4 : ℝ) ^ (1 - (k : ℝ)))⁻¹ * ‖x n‖ ^ 2 * ((discMoment (2 * n) ((k : ℝ) - 2))⁻¹ *
          discMoment (2 * n) ((k : ℝ) - 2)) := by rw [inv_mul_cancel₀ hβ, mul_one]
    _ = ((4 : ℝ) ^ (1 - (k : ℝ)) * discMoment (2 * n) ((k : ℝ) - 2))⁻¹ * ‖x n‖ ^ 2 *
          discMoment (2 * n) ((k : ℝ) - 2) := by rw [mul_inv]; ring

theorem bergmanToLp_surjective [CompleteSpace E] (hk : 2 ≤ k) :
    Function.Surjective (bergmanToLp (E := E) hk) := by
  intro f
  have hf := (BergmanAux.lp_hasSum_norm_sq f).summable
  have hl : Summable fun n : ℕ => ‖f (Sum.inl n)‖ ^ 2 := hf.comp_injective Sum.inl_injective
  have hr : Summable fun n : ℕ => ‖f (Sum.inr n)‖ ^ 2 := hf.comp_injective Sum.inr_injective
  have hc := summable_bergmanUnscale hk (fun m => f (Sum.inl m)) hl
  have hd := summable_bergmanUnscale hk (fun m => f (Sum.inr m)) hr
  refine ⟨ofCoeff hk _ _ hc hd, ?_⟩
  refine lp.ext (funext fun i => ?_)
  rcases i with n | n
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffPlus (ofCoeff hk _ _ hc hd) n = f (Sum.inl n)
    rw [coeffPlus_ofCoeff]
    show ((bergmanScale k n : ℝ) : ℂ) • (((bergmanScale k n)⁻¹ : ℝ) : ℂ) • f (Sum.inl n) =
      f (Sum.inl n)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (bergmanScale_pos hk n).ne',
      Complex.ofReal_one, one_smul]
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffMinus (ofCoeff hk _ _ hc hd) n = f (Sum.inr n)
    rw [coeffMinus_ofCoeff]
    show ((bergmanScale k n : ℝ) : ℂ) • (((bergmanScale k n)⁻¹ : ℝ) : ℂ) • f (Sum.inr n) =
      f (Sum.inr n)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (bergmanScale_pos hk n).ne',
      Complex.ofReal_one, one_smul]

/-- The linear isometry equivalence between the Bergman space and `ℓ²(ℕ ⊕ ℕ; E)`. -/
def bergmanEquivLp [CompleteSpace E] (hk : 2 ≤ k) :
    BergmanSpace k E ≃ₗᵢ[ℂ] lp (fun _ : ℕ ⊕ ℕ => E) 2 :=
  LinearIsometryEquiv.ofSurjective (bergmanToLp hk) (bergmanToLp_surjective hk)

/-- The Bergman space is complete for `2 ≤ k`. -/
instance BergmanSpace.instCompleteSpace [CompleteSpace E] [Fact (2 ≤ k)] :
    CompleteSpace (BergmanSpace k E) :=
  (bergmanEquivLp (Fact.out : 2 ≤ k)).toIsometryEquiv.completeSpace

/-- The coefficients determine the element of the Bergman space. -/
theorem eq_of_coeff [CompleteSpace E] (hk : 2 ≤ k) {F G : BergmanSpace k E}
    (hp : ∀ n, coeffPlus F n = coeffPlus G n) (hm : ∀ n, coeffMinus F n = coeffMinus G n) :
    F = G := by
  apply (bergmanToLp hk).injective
  refine lp.ext (funext fun i => ?_)
  rcases i with n | n
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffPlus F n =
      ((bergmanScale k n : ℝ) : ℂ) • coeffPlus G n
    rw [hp n]
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffMinus F n =
      ((bergmanScale k n : ℝ) : ℂ) • coeffMinus G n
    rw [hm n]

theorem bergmanToLp_apply [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) (i : ℕ ⊕ ℕ) :
    (bergmanToLp hk F) i = scaledCoeff F i :=
  rfl

theorem inner_scaledCoeff_inl (hk : 2 ≤ k) (F G : BergmanSpace k E) (n : ℕ) :
    inner ℂ (scaledCoeff F (Sum.inl n)) (scaledCoeff G (Sum.inl n)) =
      ((bergmanWeight k n : ℝ) : ℂ) * inner ℂ (coeffPlus F n) (coeffPlus G n) := by
  show inner ℂ (((bergmanScale k n : ℝ) : ℂ) • coeffPlus F n)
    (((bergmanScale k n : ℝ) : ℂ) • coeffPlus G n) = _
  rw [BergmanAux.inner_scale_smul, bergmanScale_sq hk]

theorem inner_scaledCoeff_inr (hk : 2 ≤ k) (F G : BergmanSpace k E) (n : ℕ) :
    inner ℂ (scaledCoeff F (Sum.inr n)) (scaledCoeff G (Sum.inr n)) =
      ((bergmanWeight k n : ℝ) : ℂ) * inner ℂ (coeffMinus F n) (coeffMinus G n) := by
  show inner ℂ (((bergmanScale k n : ℝ) : ℂ) • coeffMinus F n)
    (((bergmanScale k n : ℝ) : ℂ) • coeffMinus G n) = _
  rw [BergmanAux.inner_scale_smul, bergmanScale_sq hk]

theorem hasSum_inner_scaledCoeff [CompleteSpace E] (hk : 2 ≤ k) (F G : BergmanSpace k E) :
    HasSum (fun i => inner ℂ (scaledCoeff F i) (scaledCoeff G i)) (inner ℂ F G) := by
  have h1 : inner ℂ (bergmanToLp hk F) (bergmanToLp hk G) = inner ℂ F G :=
    (bergmanToLp hk).inner_map_map F G
  have hs := lp.summable_inner (𝕜 := ℂ) (bergmanToLp hk F) (bergmanToLp hk G)
  have h2 : inner ℂ (bergmanToLp hk F) (bergmanToLp hk G) =
      ∑' i, inner ℂ (scaledCoeff F i) (scaledCoeff G i) := lp.inner_eq_tsum _ _
  rw [← h1, h2]
  exact hs.hasSum

/-- **Parseval** (polarized form) for the Bergman space. -/
theorem hasSum_inner [CompleteSpace E] (hk : 2 ≤ k) (F G : BergmanSpace k E) :
    HasSum (fun n => ((bergmanWeight k n : ℝ) : ℂ) *
      (inner ℂ (coeffPlus F n) (coeffPlus G n) + inner ℂ (coeffMinus F n) (coeffMinus G n)))
      (inner ℂ F G) := by
  have h := BergmanAux.hasSum_inl_add_inr (hasSum_inner_scaledCoeff hk F G)
  have hfun : (fun n => ((bergmanWeight k n : ℝ) : ℂ) *
      (inner ℂ (coeffPlus F n) (coeffPlus G n) + inner ℂ (coeffMinus F n) (coeffMinus G n))) =
      fun n => inner ℂ (scaledCoeff F (Sum.inl n)) (scaledCoeff G (Sum.inl n)) +
        inner ℂ (scaledCoeff F (Sum.inr n)) (scaledCoeff G (Sum.inr n)) := by
    funext n
    rw [inner_scaledCoeff_inl hk, inner_scaledCoeff_inr hk]
    ring
  rw [hfun]
  exact h

/-- The `n`-th upper coefficient is bounded by `(√(4^(1-k) βₙ))⁻¹ ‖F‖`. -/
theorem norm_coeffPlus_le [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) (n : ℕ) :
    ‖coeffPlus F n‖ ≤ (bergmanScale k n)⁻¹ * ‖F‖ := by
  have h := lp.norm_apply_le_norm (p := 2) (by norm_num) ((bergmanToLp hk) F) (Sum.inl n)
  rw [(bergmanToLp hk).norm_map] at h
  have h' : ‖((bergmanScale k n : ℝ) : ℂ) • coeffPlus F n‖ ≤ ‖F‖ := h
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (bergmanScale_nonneg k n)] at h'
  rw [inv_mul_eq_div, le_div_iff₀ (bergmanScale_pos hk n)]
  linarith

/-- The `n`-th lower coefficient is bounded by `(√(4^(1-k) βₙ))⁻¹ ‖F‖`. -/
theorem norm_coeffMinus_le [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) (n : ℕ) :
    ‖coeffMinus F n‖ ≤ (bergmanScale k n)⁻¹ * ‖F‖ := by
  have h := lp.norm_apply_le_norm (p := 2) (by norm_num) ((bergmanToLp hk) F) (Sum.inr n)
  rw [(bergmanToLp hk).norm_map] at h
  have h' : ‖((bergmanScale k n : ℝ) : ℂ) • coeffMinus F n‖ ≤ ‖F‖ := h
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (bergmanScale_nonneg k n)] at h'
  rw [inv_mul_eq_div, le_div_iff₀ (bergmanScale_pos hk n)]
  linarith

/-- The `n`-th upper coefficient as a continuous linear map. -/
def coeffPlusL [CompleteSpace E] (hk : 2 ≤ k) (n : ℕ) : BergmanSpace k E →L[ℂ] E :=
  LinearMap.mkContinuous
    ({ toFun := fun F => coeffPlus F n
       map_add' := fun F G => coeffPlus_add F G n
       map_smul' := fun c F => coeffPlus_smul c F n } : BergmanSpace k E →ₗ[ℂ] E)
    (bergmanScale k n)⁻¹ (fun F => norm_coeffPlus_le hk F n)

/-- The `n`-th lower coefficient as a continuous linear map. -/
def coeffMinusL [CompleteSpace E] (hk : 2 ≤ k) (n : ℕ) : BergmanSpace k E →L[ℂ] E :=
  LinearMap.mkContinuous
    ({ toFun := fun F => coeffMinus F n
       map_add' := fun F G => coeffMinus_add F G n
       map_smul' := fun c F => coeffMinus_smul c F n } : BergmanSpace k E →ₗ[ℂ] E)
    (bergmanScale k n)⁻¹ (fun F => norm_coeffMinus_le hk F n)

@[simp] theorem coeffPlusL_apply [CompleteSpace E] (hk : 2 ≤ k) (n : ℕ) (F : BergmanSpace k E) :
    coeffPlusL hk n F = coeffPlus F n :=
  rfl

@[simp] theorem coeffMinusL_apply [CompleteSpace E] (hk : 2 ≤ k) (n : ℕ) (F : BergmanSpace k E) :
    coeffMinusL hk n F = coeffMinus F n :=
  rfl

end Hilbert

section PointMass

variable {E : Type*} [NormedAddCommGroup E]

/-- The sequence with value `x` at index `0` and `0` elsewhere. -/
def bergmanPointMass (x : E) : ℕ → E := fun n => if n = 0 then x else 0

theorem summable_bergmanPointMass (k : ℕ) (x : E) :
    Summable fun n => ‖bergmanPointMass x n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2) := by
  refine (hasSum_single 0 (fun n hn => ?_)).summable
  simp [bergmanPointMass, hn]

end PointMass

section Lowest

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem upperSeries_bergmanPointMass (x : E) (z : ℂ) :
    upperSeries k (bergmanPointMass x) z = ((z + Complex.I) ^ k)⁻¹ • x := by
  unfold upperSeries
  congr 1
  rw [tsum_eq_single 0]
  · simp [bergmanPointMass]
  · intro n hn
    simp [bergmanPointMass, hn]

theorem upperSeries_zero (z : ℂ) :
    upperSeries k (fun _ => (0 : E)) z = 0 := by
  simp [upperSeries]

/-- The lowest weight vector `w ↦ ((w - i)^k)⁻¹ • e` of the lower half plane (zero on the upper
half plane and on the real axis). -/
def lowestMinus [CompleteSpace E] (hk : 2 ≤ k) (e : E) : BergmanSpace k E :=
  ofCoeff hk (fun _ => 0) (bergmanPointMass (((-1 : ℂ) ^ k) • e))
    (BergmanAux.summable_zeroSeq k) (summable_bergmanPointMass k _)

/-- The lowest weight vector `w ↦ ((w + i)^k)⁻¹ • e` of the upper half plane (zero on the lower
half plane and on the real axis). -/
def lowestPlus [CompleteSpace E] (hk : 2 ≤ k) (e : E) : BergmanSpace k E :=
  ofCoeff hk (bergmanPointMass e) (fun _ => 0) (summable_bergmanPointMass k _)
    (BergmanAux.summable_zeroSeq k)

theorem coeffMinus_lowestMinus [CompleteSpace E] (hk : 2 ≤ k) (e : E) (n : ℕ) :
    coeffMinus (lowestMinus hk e) n = if n = 0 then ((-1 : ℂ) ^ k) • e else 0 :=
  coeffMinus_ofCoeff hk _ _ (BergmanAux.summable_zeroSeq k) (summable_bergmanPointMass k _) n

theorem coeffPlus_lowestMinus [CompleteSpace E] (hk : 2 ≤ k) (e : E) (n : ℕ) :
    coeffPlus (lowestMinus hk e) n = 0 :=
  coeffPlus_ofCoeff hk _ _ (BergmanAux.summable_zeroSeq k) (summable_bergmanPointMass k _) n

theorem coeffPlus_lowestPlus [CompleteSpace E] (hk : 2 ≤ k) (e : E) (n : ℕ) :
    coeffPlus (lowestPlus hk e) n = if n = 0 then e else 0 :=
  coeffPlus_ofCoeff hk _ _ (summable_bergmanPointMass k _) (BergmanAux.summable_zeroSeq k) n

theorem coeffMinus_lowestPlus [CompleteSpace E] (hk : 2 ≤ k) (e : E) (n : ℕ) :
    coeffMinus (lowestPlus hk e) n = 0 :=
  coeffMinus_ofCoeff hk _ _ (summable_bergmanPointMass k _) (BergmanAux.summable_zeroSeq k) n

theorem lowestMinus_apply [CompleteSpace E] (hk : 2 ≤ k) (e : E) (w : ℂ) :
    lowestMinus hk e w = if w.im < 0 then ((w - Complex.I) ^ k)⁻¹ • e else 0 := by
  show ofCoeffFun k (fun _ => (0 : E)) (bergmanPointMass (((-1 : ℂ) ^ k) • e)) w = _
  rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
  · rw [ofCoeffFun_of_neg hneg, upperSeries_bergmanPointMass, ite_eq_left hneg]
    have hne : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h : -w + Complex.I = -(w - Complex.I) := by ring
    rw [h, neg_pow, smul_smul]
    congr 1
    rw [mul_inv, mul_comm ((-1 : ℂ) ^ k)⁻¹, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  · rw [ofCoeffFun_of_eq hzero, ite_eq_right (not_lt.2 hzero.ge)]
  · rw [ofCoeffFun_of_pos hpos, upperSeries_zero, ite_eq_right (not_lt.2 hpos.le)]

theorem lowestPlus_apply [CompleteSpace E] (hk : 2 ≤ k) (e : E) (w : ℂ) :
    lowestPlus hk e w = if 0 < w.im then ((w + Complex.I) ^ k)⁻¹ • e else 0 := by
  show ofCoeffFun k (bergmanPointMass e) (fun _ => (0 : E)) w = _
  rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
  · rw [ofCoeffFun_of_neg hneg, upperSeries_zero, ite_eq_right (not_lt.2 hneg.le)]
  · rw [ofCoeffFun_of_eq hzero, ite_eq_right (not_lt.2 hzero.le)]
  · rw [ofCoeffFun_of_pos hpos, upperSeries_bergmanPointMass, ite_eq_left hpos]

end Lowest

end TernaryPeriodPolynomials.Regularity

end
