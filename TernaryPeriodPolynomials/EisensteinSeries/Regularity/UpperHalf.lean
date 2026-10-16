module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Disc
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Jacobian

@[expose] public section


/-!
# Holomorphic functions on the upper half plane through the unit disc

For `G` holomorphic on the upper half plane, the disc transform
`discTransform k G ζ = (icay ζ + i)^k • G (icay ζ)` is holomorphic on the unit disc and
`upperCoeff k G n` is its `n`-th Taylor coefficient.  The change of variables
`z = icay ζ` (with `z + i = 2 i / (1 - ζ)` and `Im z = (1 - |ζ|²) / |1 - ζ|²`) turns the weighted
integrals over the upper half plane into the radial integrals of `Disc.lean`, giving:

* the Parseval identity `lintegral_upper_norm_sq` and the `L¹` bound `lintegral_upper_norm_le`;
* the reconstruction `upperSeries k c` of a function from coefficients of polynomial growth;
* linearity, continuous-linear-map and rotation compatibility of the coefficients;
* the coefficients of the lowest weight vector and of the value at `i`;
* the reproducing formula `integral_upper_reproducing` for bounded weighted holomorphic `h`.
-/

noncomputable section

open Complex MeasureTheory

namespace TernaryPeriodPolynomials.Regularity

/-! ### Elementary facts on the disc -/

private lemma ne_one_of_norm_lt_one {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ζ ≠ 1 := by
  rintro rfl
  simp at hζ

private lemma norm_one_sub_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 0 < ‖1 - ζ‖ :=
  norm_pos_iff.2 (sub_ne_zero.2 (ne_one_of_norm_lt_one hζ).symm)

private lemma one_sub_norm_sq_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 0 < 1 - ‖ζ‖ ^ 2 := by
  have h0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  nlinarith

private lemma add_I_ne_zero {z : ℂ} (hz : z ∈ upper) : z + I ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 : 0 < z.im := hz
  simp at h1
  linarith

private lemma icay_add_I_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ < 1) : icay ζ + I ≠ 0 := by
  rw [icay_add_I (ne_one_of_norm_lt_one hζ)]
  exact div_ne_zero (by simp) (sub_ne_zero.2 (ne_one_of_norm_lt_one hζ).symm)

private lemma norm_icay_add_I {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ‖icay ζ + I‖ = 2 / ‖1 - ζ‖ := by
  rw [icay_add_I (ne_one_of_norm_lt_one hζ), norm_div]
  simp

private lemma mem_ball_of_mem_sphere_half {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) (1 / 2)) :
    z ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm] at hz
  rw [mem_ball_zero_iff, hz]
  norm_num

private lemma rpow_sub_two {s : ℝ} (hs : 0 < s) (k : ℕ) : s ^ ((k : ℝ) - 2) = s ^ k / s ^ 2 := by
  rw [Real.rpow_sub hs, Real.rpow_natCast, Real.rpow_two]

private lemma rpow_half_sub_two {s : ℝ} (hs : 0 < s) (k : ℕ) :
    s ^ ((k : ℝ) / 2 - 2) = s ^ ((k : ℝ) / 2) / s ^ 2 := by
  rw [Real.rpow_sub hs, Real.rpow_two]

private lemma sq_rpow_half {d : ℝ} (hd : 0 < d) (k : ℕ) : (d ^ 2) ^ ((k : ℝ) / 2) = d ^ k := by
  rw [← Real.rpow_natCast d 2, ← Real.rpow_mul hd.le]
  have : ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast]

private lemma four_rpow_one_sub (k : ℕ) : (4 : ℝ) ^ (1 - (k : ℝ)) = 4 / 4 ^ k := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 4), Real.rpow_one, Real.rpow_natCast]

private lemma two_rpow_two_sub (k : ℕ) : (2 : ℝ) ^ (2 - (k : ℝ)) = 4 / 2 ^ k := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_two, Real.rpow_natCast]
  norm_num

private lemma four_pow_eq (k : ℕ) : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
  rw [sq, ← mul_pow]
  norm_num

private lemma continuousOn_weight (a : ℝ) :
    ContinuousOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ a) (Metric.ball 0 1) := by
  refine ContinuousOn.rpow_const ?_
    (fun ζ hζ => Or.inl (one_sub_norm_sq_pos (mem_ball_zero_iff.1 hζ)).ne')
  exact (continuous_const.sub (continuous_norm.pow 2)).continuousOn

/-! ### The disc transform -/

section Pure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ} {G : ℂ → E}

/-- The disc transform of a holomorphic function on the upper half plane is holomorphic on the
unit disc. -/
theorem differentiableOn_discTransform (hG : DifferentiableOn ℂ G upper) :
    DifferentiableOn ℂ (discTransform k G) (Metric.ball 0 1) := by
  have hi : DifferentiableOn ℂ icay (Metric.ball 0 1) := differentiableOn_icay
  have h1 : DifferentiableOn ℂ (fun ζ => (icay ζ + I) ^ k) (Metric.ball 0 1) :=
    (hi.add_const I).pow k
  have h2 : DifferentiableOn ℂ (fun ζ => G (icay ζ)) (Metric.ball 0 1) :=
    hG.comp hi (fun ζ hζ => icay_mem_upper (mem_ball_zero_iff.1 hζ))
  exact h1.smul h2

/-- A function on the upper half plane is recovered from its disc transform. -/
theorem eq_discTransform_cay {z : ℂ} (hz : z ∈ upper) :
    G z = ((z + I) ^ k)⁻¹ • discTransform k G (cay z) := by
  rw [discTransform, icay_cay (add_I_ne_zero hz), smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ (add_I_ne_zero hz)), one_smul]

private lemma continuousOn_discTransform (hG : ContinuousOn G upper) :
    ContinuousOn (discTransform k G) (Metric.ball 0 1) := by
  have hi : ContinuousOn icay (Metric.ball 0 1) := differentiableOn_icay.continuousOn
  have h1 : ContinuousOn (fun ζ => (icay ζ + I) ^ k) (Metric.ball 0 1) :=
    (hi.add continuousOn_const).pow k
  have h2 : ContinuousOn (fun ζ => G (icay ζ)) (Metric.ball 0 1) :=
    hG.comp hi (fun ζ hζ => icay_mem_upper (mem_ball_zero_iff.1 hζ))
  exact h1.smul h2

private lemma continuousOn_discTransform_sphere (hG : ContinuousOn G upper) :
    ContinuousOn (discTransform k G) (Metric.sphere 0 (1 / 2)) :=
  (continuousOn_discTransform hG).mono (fun _ hz => mem_ball_of_mem_sphere_half hz)

private lemma discTransform_zero (G : ℂ → E) :
    discTransform k G 0 = (2 * I) ^ k • G I := by
  simp only [discTransform, icay_zero]
  rw [← two_mul]

private lemma norm_discTransform {ζ : ℂ} (hζ : ‖ζ‖ < 1) (G : ℂ → E) (k : ℕ) :
    ‖discTransform k G ζ‖ = (2 / ‖1 - ζ‖) ^ k * ‖G (icay ζ)‖ := by
  rw [discTransform, norm_smul, norm_pow, norm_icay_add_I hζ]

private lemma weight_sq_eq {ζ : ℂ} (hζ : ‖ζ‖ < 1) (G : ℂ → E) (k : ℕ) :
    4 / (1 - ‖ζ‖ ^ 2) ^ 2 * (‖G (icay ζ)‖ ^ 2 * (icay ζ).im ^ k) =
      (4 : ℝ) ^ (1 - (k : ℝ)) *
        (‖discTransform k G ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2)) := by
  have hs := one_sub_norm_sq_pos hζ
  have hd := norm_one_sub_pos hζ
  have hs' : 1 - ‖ζ‖ ^ 2 ≠ 0 := hs.ne'
  have hd' : ‖1 - ζ‖ ≠ 0 := hd.ne'
  rw [norm_discTransform hζ, im_icay (ne_one_of_norm_lt_one hζ), rpow_sub_two hs k,
    four_rpow_one_sub, four_pow_eq]
  simp only [div_pow]
  field_simp
  ring

private lemma weight_abs_eq {ζ : ℂ} (hζ : ‖ζ‖ < 1) (G : ℂ → E) (k : ℕ) :
    4 / (1 - ‖ζ‖ ^ 2) ^ 2 * (‖G (icay ζ)‖ * (icay ζ).im ^ ((k : ℝ) / 2)) =
      (2 : ℝ) ^ (2 - (k : ℝ)) *
        (‖discTransform k G ζ‖ * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2)) := by
  have hs := one_sub_norm_sq_pos hζ
  have hd := norm_one_sub_pos hζ
  have hs' : 1 - ‖ζ‖ ^ 2 ≠ 0 := hs.ne'
  have hd' : ‖1 - ζ‖ ≠ 0 := hd.ne'
  rw [norm_discTransform hζ, im_icay (ne_one_of_norm_lt_one hζ),
    Real.div_rpow hs.le (sq_nonneg _), sq_rpow_half hd, rpow_half_sub_two hs k,
    two_rpow_two_sub k, div_pow]
  field_simp

private lemma norm_discTransform_mul_le {C : ℝ}
    (hC : ∀ z ∈ upper, ‖G z‖ * z.im ^ ((k : ℝ) / 2) ≤ C) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖discTransform k G ζ‖ * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ 2 ^ k * C := by
  have hs := one_sub_norm_sq_pos hζ
  have hd := norm_one_sub_pos hζ
  have h1 := hC (icay ζ) (icay_mem_upper hζ)
  rw [im_icay (ne_one_of_norm_lt_one hζ), Real.div_rpow hs.le (sq_nonneg _),
    sq_rpow_half hd] at h1
  rw [norm_discTransform hζ, div_pow]
  calc 2 ^ k / ‖1 - ζ‖ ^ k * ‖G (icay ζ)‖ * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2)
      = 2 ^ k * (‖G (icay ζ)‖ * ((1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2) / ‖1 - ζ‖ ^ k)) := by ring
    _ ≤ 2 ^ k * C := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The function on the upper half plane with coefficients `c`:
`((z + i)^k)⁻¹ • ∑ cₙ (cay z)ⁿ`. -/
def upperSeries (k : ℕ) (c : ℕ → E) (z : ℂ) : E :=
  ((z + I) ^ k)⁻¹ • ∑' n, cay z ^ n • c n

end Pure

/-! ### Circle-integral calculus of the Taylor coefficients -/

section Circle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private lemma taylorCoeff_eq_circleIntegral (H : ℂ → E) (n : ℕ) :
    taylorCoeff H n = (2 * Real.pi * I : ℂ)⁻¹ •
      circleIntegral (fun z : ℂ => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • H z) 0 (1 / 2) := by
  unfold taylorCoeff
  exact cauchyPowerSeries_apply H 0 (1 / 2) n 1

omit [CompleteSpace E] in
private lemma continuousOn_kernel {H : ℂ → E} (hH : ContinuousOn H (Metric.sphere 0 (1 / 2)))
    (n : ℕ) :
    ContinuousOn (fun z : ℂ => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • H z)
      (Metric.sphere 0 (1 / 2)) := by
  have hz : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), z - 0 ≠ 0 := by
    intro z hz h
    rw [mem_sphere_zero_iff_norm] at hz
    rw [sub_zero] at h
    rw [h, norm_zero] at hz
    norm_num at hz
  have hid : ContinuousOn (fun z : ℂ => z - 0) (Metric.sphere 0 (1 / 2)) :=
    continuousOn_id.sub continuousOn_const
  refine ContinuousOn.smul ?_ (ContinuousOn.smul ?_ hH)
  · exact (continuousOn_const.div hid hz).pow n
  · exact hid.inv₀ hz

omit [CompleteSpace E] in
private lemma circleIntegrable_kernel {H : ℂ → E} (hH : ContinuousOn H (Metric.sphere 0 (1 / 2)))
    (n : ℕ) :
    CircleIntegrable (fun z : ℂ => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • H z) 0 (1 / 2) :=
  (continuousOn_kernel hH n).circleIntegrable (by norm_num)

omit [CompleteSpace E] in
private lemma taylorCoeff_congr_ball {H H' : ℂ → E} (h : Set.EqOn H H' (Metric.ball 0 1))
    (n : ℕ) : taylorCoeff H n = taylorCoeff H' n := by
  rw [taylorCoeff_eq_circleIntegral, taylorCoeff_eq_circleIntegral]
  congr 1
  refine circleIntegral.integral_congr (by norm_num) (fun z hz => ?_)
  simp only [h (mem_ball_of_mem_sphere_half hz)]

omit [CompleteSpace E] in
private lemma taylorCoeff_add_circle {H H' : ℂ → E}
    (hH : ContinuousOn H (Metric.sphere 0 (1 / 2)))
    (hH' : ContinuousOn H' (Metric.sphere 0 (1 / 2))) (n : ℕ) :
    taylorCoeff (fun ζ => H ζ + H' ζ) n = taylorCoeff H n + taylorCoeff H' n := by
  simp only [taylorCoeff_eq_circleIntegral]
  rw [← smul_add]
  congr 1
  have hadd := circleIntegral.integral_add (circleIntegrable_kernel hH n)
    (circleIntegrable_kernel hH' n)
  rw [← hadd]
  refine circleIntegral.integral_congr (by norm_num) (fun z _ => ?_)
  simp only [smul_add]

omit [CompleteSpace E] in
private lemma taylorCoeff_smul_circle (a : ℂ) (H : ℂ → E) (n : ℕ) :
    taylorCoeff (fun ζ => a • H ζ) n = a • taylorCoeff H n := by
  simp only [taylorCoeff_eq_circleIntegral]
  have h : circleIntegral (fun z : ℂ => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • a • H z) 0 (1 / 2) =
      a • circleIntegral (fun z : ℂ => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • H z) 0 (1 / 2) := by
    rw [← circleIntegral.integral_smul]
    refine circleIntegral.integral_congr (by norm_num) (fun z _ => ?_)
    show (1 / (z - 0)) ^ n • (z - 0)⁻¹ • a • H z = a • ((1 / (z - 0)) ^ n • (z - 0)⁻¹ • H z)
    rw [smul_comm ((z - 0)⁻¹) a (H z), smul_comm ((1 / (z - 0)) ^ n) a ((z - 0)⁻¹ • H z)]
  rw [h]
  exact smul_comm _ _ _

private lemma taylorCoeff_clm_circle {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [CompleteSpace E']
    (L : E →L[ℂ] E') {H : ℂ → E} (hH : ContinuousOn H (Metric.sphere 0 (1 / 2))) (n : ℕ) :
    taylorCoeff (fun ζ => L (H ζ)) n = L (taylorCoeff H n) := by
  simp only [taylorCoeff_eq_circleIntegral]
  rw [map_smul]
  congr 1
  have hint := (circleIntegrable_kernel hH n).out
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hint]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [map_smul]

end Circle

/-! ### Coefficients: congruence, linearity and special vectors -/

section Coefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {k : ℕ}
  {G G' : ℂ → E}

omit [CompleteSpace E] in
/-- Coefficients only depend on the values on the upper half plane. -/
theorem upperCoeff_congr (h : Set.EqOn G G' upper) (n : ℕ) :
    upperCoeff k G n = upperCoeff k G' n := by
  unfold upperCoeff
  refine taylorCoeff_congr_ball (fun ζ hζ => ?_) n
  simp only [discTransform]
  rw [h (icay_mem_upper (mem_ball_zero_iff.1 hζ))]

omit [CompleteSpace E] in
theorem upperCoeff_add (hG : ContinuousOn G upper) (hG' : ContinuousOn G' upper) (n : ℕ) :
    upperCoeff k (fun z => G z + G' z) n = upperCoeff k G n + upperCoeff k G' n := by
  have h : discTransform k (fun z => G z + G' z) =
      fun ζ => discTransform k G ζ + discTransform k G' ζ := by
    funext ζ
    simp only [discTransform, smul_add]
  unfold upperCoeff
  rw [h]
  exact taylorCoeff_add_circle (continuousOn_discTransform_sphere hG)
    (continuousOn_discTransform_sphere hG') n

omit [CompleteSpace E] in
theorem upperCoeff_smul (a : ℂ) (n : ℕ) :
    upperCoeff k (fun z => a • G z) n = a • upperCoeff k G n := by
  have h : discTransform k (fun z => a • G z) = fun ζ => a • discTransform k G ζ := by
    funext ζ
    simp only [discTransform]
    exact smul_comm _ _ _
  unfold upperCoeff
  rw [h]
  exact taylorCoeff_smul_circle a _ n

omit [CompleteSpace E] in
theorem upperCoeff_sub (hG : ContinuousOn G upper) (hG' : ContinuousOn G' upper) (n : ℕ) :
    upperCoeff k (fun z => G z - G' z) n = upperCoeff k G n - upperCoeff k G' n := by
  have h : (fun z => G z - G' z) = fun z => G z + (-1 : ℂ) • G' z := by
    funext z
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h, upperCoeff_add (G' := fun z => (-1 : ℂ) • G' z) hG (hG'.const_smul (-1 : ℂ)),
    upperCoeff_smul, neg_one_smul,
    sub_eq_add_neg]

/-- The coefficient functional of a continuous linear map applied to a function. -/
theorem upperCoeff_comp_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [CompleteSpace E']
    (L : E →L[ℂ] E') (hG : ContinuousOn G upper) (n : ℕ) :
    upperCoeff k (fun z => L (G z)) n = L (upperCoeff k G n) := by
  have h : discTransform k (fun z => L (G z)) = fun ζ => L (discTransform k G ζ) := by
    funext ζ
    simp only [discTransform, map_smul]
  unfold upperCoeff
  rw [h]
  exact taylorCoeff_clm_circle L (continuousOn_discTransform_sphere hG) n

/-- The coefficients of the lowest weight vector `((z + i)^k)⁻¹ • e`. -/
theorem upperCoeff_lowest (e : E) (n : ℕ) :
    upperCoeff k (fun z => ((z + I) ^ k)⁻¹ • e) n = if n = 0 then e else 0 := by
  have h : Set.EqOn (discTransform k (fun z => ((z + I) ^ k)⁻¹ • e)) (fun _ => e)
      (Metric.ball 0 1) := by
    intro ζ hζ
    have hζ' := mem_ball_zero_iff.1 hζ
    simp only [discTransform]
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ (icay_add_I_ne_zero hζ')), one_smul]
  unfold upperCoeff
  rw [taylorCoeff_congr_ball h]
  exact taylorCoeff_const e n

theorem upperCoeff_zero_fun (n : ℕ) : upperCoeff k (fun _ : ℂ => (0 : E)) n = 0 := by
  have h := upperCoeff_lowest (k := k) (0 : E) n
  simpa using h

/-- The coefficient of index `0` is the value at `i`, up to the factor `(2 i)^k`. -/
theorem upperCoeff_zero_eq (hG : DifferentiableOn ℂ G upper) :
    upperCoeff k G 0 = (2 * I) ^ k • G I := by
  unfold upperCoeff
  rw [taylorCoeff_zero_eq (differentiableOn_discTransform hG), discTransform_zero]

/-! ### Reconstruction -/

/-- A series with polynomially bounded coefficients defines a holomorphic function on the upper
half plane. -/
theorem differentiableOn_upperSeries {c : ℕ → E} {C : ℝ} {N : ℕ}
    (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ N) : DifferentiableOn ℂ (upperSeries k c) upper := by
  have hS := differentiableOn_tsum_of_bound hc
  have hcay : DifferentiableOn ℂ cay upper := differentiableOn_cay
  have h1 : DifferentiableOn ℂ (fun z : ℂ => ((z + I) ^ k)⁻¹) upper :=
    ((differentiableOn_id.add_const I).pow k).inv (fun z hz => pow_ne_zero _ (add_I_ne_zero hz))
  have h2 : DifferentiableOn ℂ (fun z : ℂ => ∑' n, cay z ^ n • c n) upper :=
    hS.comp hcay (fun z hz => mem_ball_zero_iff.2 (norm_cay_lt_one hz))
  exact h1.smul h2

/-- The coefficients of `upperSeries k c` are `c`. -/
theorem upperCoeff_upperSeries {c : ℕ → E} {C : ℝ} {N : ℕ}
    (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ N) (n : ℕ) :
    upperCoeff k (upperSeries k c) n = c n := by
  have h : Set.EqOn (discTransform k (upperSeries k c)) (fun ζ => ∑' n, ζ ^ n • c n)
      (Metric.ball 0 1) := by
    intro ζ hζ
    have hζ' : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    simp only [discTransform, upperSeries]
    rw [cay_icay (ne_one_of_norm_lt_one hζ'), smul_smul,
      mul_inv_cancel₀ (pow_ne_zero _ (icay_add_I_ne_zero hζ')), one_smul]
  unfold upperCoeff
  rw [taylorCoeff_congr_ball h]
  exact taylorCoeff_tsum_of_bound hc n

/-- A holomorphic function is the series of its coefficients. -/
theorem upperSeries_upperCoeff (hG : DifferentiableOn ℂ G upper) {z : ℂ} (hz : z ∈ upper) :
    upperSeries k (upperCoeff k G) z = G z := by
  have hH := differentiableOn_discTransform (k := k) hG
  have h := (hasSum_taylorCoeff hH (norm_cay_lt_one hz)).tsum_eq
  unfold upperSeries upperCoeff
  rw [h]
  exact (eq_discTransform_cay hz).symm

/-! ### Rotations -/

/-- The coefficients of `z ↦ (denom (rotGL θ) z ^ k)⁻¹ • G (moeb (rotGL θ) z)` are those of `G`
multiplied by the characters `e^{-i(k + 2n)θ}`. -/
theorem upperCoeff_rot (θ : ℝ) (hG : DifferentiableOn ℂ G upper) (n : ℕ) :
    upperCoeff k (fun z => (denom (rotGL θ) z ^ k)⁻¹ • G (moeb (rotGL θ) z)) n =
      Complex.exp (-(((k : ℂ) + 2 * n) * θ) * I) • upperCoeff k G n := by
  have hH := differentiableOn_discTransform (k := k) hG
  have hu : ‖Complex.exp (-(2 * θ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have h : Set.EqOn
      (discTransform k (fun z => (denom (rotGL θ) z ^ k)⁻¹ • G (moeb (rotGL θ) z)))
      (fun ζ => Complex.exp (-((k : ℂ) * θ) * I) •
        discTransform k G (Complex.exp (-(2 * θ) * I) * ζ)) (Metric.ball 0 1) := by
    intro ζ hζ
    have hζ' := mem_ball_zero_iff.1 hζ
    have hz : 0 < (icay ζ).im := icay_mem_upper hζ'
    have hd : denom (rotGL θ) (icay ζ) ≠ 0 := denom_ne_zero _ hz.ne'
    have hw : moeb (rotGL θ) (icay ζ) ∈ upper :=
      moeb_mem_upper _ (by rw [det_rotGL]; exact one_pos) hz
    have hcay : cay (moeb (rotGL θ) (icay ζ)) = Complex.exp (-(2 * θ) * I) * ζ := by
      rw [cay_moeb_rotGL θ hz, cay_icay (ne_one_of_norm_lt_one hζ')]
    have hrel := denom_rotGL_mul_add_I θ hd
    have hz1 : icay ζ + I = Complex.exp (-(θ : ℂ) * I) *
        (denom (rotGL θ) (icay ζ) * (moeb (rotGL θ) (icay ζ) + I)) := by
      rw [hrel, ← mul_assoc, ← Complex.exp_add, show -(θ : ℂ) * I + θ * I = 0 by ring,
        Complex.exp_zero, one_mul]
    have key : (icay ζ + I) ^ k * (denom (rotGL θ) (icay ζ) ^ k)⁻¹ =
        Complex.exp (-((k : ℂ) * θ) * I) * (moeb (rotGL θ) (icay ζ) + I) ^ k := by
      have hexp : Complex.exp (-((k : ℂ) * θ) * I) = Complex.exp (-(θ : ℂ) * I) ^ k := by
        rw [← Complex.exp_nat_mul]
        congr 1
        ring
      have hdk : denom (rotGL θ) (icay ζ) ^ k ≠ 0 := pow_ne_zero _ hd
      rw [hexp, hz1, mul_pow, mul_pow]
      calc Complex.exp (-(θ : ℂ) * I) ^ k * (denom (rotGL θ) (icay ζ) ^ k *
            (moeb (rotGL θ) (icay ζ) + I) ^ k) * (denom (rotGL θ) (icay ζ) ^ k)⁻¹
          = Complex.exp (-(θ : ℂ) * I) ^ k * (moeb (rotGL θ) (icay ζ) + I) ^ k *
            (denom (rotGL θ) (icay ζ) ^ k * (denom (rotGL θ) (icay ζ) ^ k)⁻¹) := by ring
        _ = Complex.exp (-(θ : ℂ) * I) ^ k * (moeb (rotGL θ) (icay ζ) + I) ^ k := by
            rw [mul_inv_cancel₀ hdk, mul_one]
    simp only [discTransform]
    rw [← hcay, icay_cay (add_I_ne_zero hw), smul_smul, smul_smul, key]
  have hscalar : Complex.exp (-((k : ℂ) * θ) * I) * Complex.exp (-(2 * θ) * I) ^ n =
      Complex.exp (-(((k : ℂ) + 2 * n) * θ) * I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  unfold upperCoeff
  rw [taylorCoeff_congr_ball h, taylorCoeff_comp_mul hH hu _ n, hscalar]

end Coefficients

/-! ### Parseval and the `L¹` bound -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {k : ℕ}
  {G : ℂ → E}

/-- **Parseval** on the upper half plane: the weighted `L²` norm of `G` is
`4^(1-k) ∑ ‖aₙ‖² βₙ` in terms of its coefficients. -/
theorem lintegral_upper_norm_sq (hk : 2 ≤ k) (hG : DifferentiableOn ℂ G upper) :
    ∫⁻ z in upper, ENNReal.ofReal (‖G z‖ ^ 2 * z.im ^ k) ∂hypMeasure =
      ∑' n, ENNReal.ofReal ((4 : ℝ) ^ (1 - (k : ℝ)) *
        (‖upperCoeff k G n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2))) := by
  have hH := differentiableOn_discTransform (k := k) hG
  have ha : (-1 : ℝ) < (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB : (0 : ℝ) ≤ (4 : ℝ) ^ (1 - (k : ℝ)) := by positivity
  unfold upperCoeff
  rw [lintegral_upper_eq_disc (fun z => ENNReal.ofReal (‖G z‖ ^ 2 * z.im ^ k))]
  have h1 : ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2) *
        ENNReal.ofReal (‖G (icay ζ)‖ ^ 2 * (icay ζ).im ^ k) =
      ENNReal.ofReal ((4 : ℝ) ^ (1 - (k : ℝ))) *
        ENNReal.ofReal (‖discTransform k G ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2)) := by
    intro ζ hζ
    have hζ' := mem_ball_zero_iff.1 hζ
    have hA : (0 : ℝ) ≤ 4 / (1 - ‖ζ‖ ^ 2) ^ 2 := by positivity
    rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB, weight_sq_eq hζ']
  rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet h1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_norm_sq_eq_tsum hH ((k : ℝ) - 2) ha, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [← ENNReal.ofReal_mul hB]

/-- The `L¹` bound on the upper half plane: `∫ ‖G‖ (Im z)^(k/2) dμ ≤ 2^(2-k) ∑ ‖aₙ‖ γₙ`. -/
theorem lintegral_upper_norm_le (hk : 3 ≤ k) (hG : DifferentiableOn ℂ G upper) :
    ∫⁻ z in upper, ENNReal.ofReal (‖G z‖ * z.im ^ ((k : ℝ) / 2)) ∂hypMeasure ≤
      ∑' n, ENNReal.ofReal ((2 : ℝ) ^ (2 - (k : ℝ)) *
        (‖upperCoeff k G n‖ * discMoment n ((k : ℝ) / 2 - 2))) := by
  have hH := differentiableOn_discTransform (k := k) hG
  have ha : (-1 : ℝ) < (k : ℝ) / 2 - 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (2 - (k : ℝ)) := by positivity
  unfold upperCoeff
  rw [lintegral_upper_eq_disc (fun z => ENNReal.ofReal (‖G z‖ * z.im ^ ((k : ℝ) / 2)))]
  have h1 : ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2) *
        ENNReal.ofReal (‖G (icay ζ)‖ * (icay ζ).im ^ ((k : ℝ) / 2)) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 - (k : ℝ))) *
        ENNReal.ofReal (‖discTransform k G ζ‖ * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2)) := by
    intro ζ hζ
    have hζ' := mem_ball_zero_iff.1 hζ
    have hA : (0 : ℝ) ≤ 4 / (1 - ‖ζ‖ ^ 2) ^ 2 := by positivity
    rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB, weight_abs_eq hζ']
  rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet h1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal ((2 : ℝ) ^ (2 - (k : ℝ))) *
        ∫⁻ ζ in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (‖discTransform k G ζ‖ * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 - (k : ℝ))) *
        ∑' n, ENNReal.ofReal (‖taylorCoeff (discTransform k G) n‖ *
          discMoment n ((k : ℝ) / 2 - 2)) :=
        mul_le_mul' le_rfl (lintegral_norm_le_tsum hH ((k : ℝ) / 2 - 2) ha)
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun n => ?_)
        rw [← ENNReal.ofReal_mul hB]

end Hilbert

/-! ### Polynomial bound from square-summability -/

section Bound

variable {E : Type*} [NormedAddCommGroup E] {k : ℕ}

/-- Square-summability against the moments `βₙ` forces polynomial growth of the coefficients. -/
theorem exists_bound_of_summable (hk : 2 ≤ k) {c : ℕ → E}
    (hs : Summable fun n => ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2)) :
    ∃ C : ℝ, ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hmom : ∀ n : ℕ, Real.pi * (Nat.factorial (k - 2) : ℝ) / ((n : ℝ) + k) ^ (k - 1) ≤
      discMoment (2 * n) ((k : ℝ) - 2) := fun n => discMoment_two_mul_ge k n hk
  have hF : 0 < Real.pi * (Nat.factorial (k - 2) : ℝ) :=
    mul_pos Real.pi_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
  have hnk : ∀ n : ℕ, 0 < ((n : ℝ) + k) ^ (k - 1) := fun n => by
    have h0 : (0 : ℝ) < (n : ℝ) + k := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact pow_pos h0 _
  have hnn : ∀ n : ℕ, 0 ≤ discMoment (2 * n) ((k : ℝ) - 2) := fun n =>
    discMoment_nonneg _ _
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ n, ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2) ≤ M := by
    refine ⟨∑' n, ‖c n‖ ^ 2 * discMoment (2 * n) ((k : ℝ) - 2),
      tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (hnn n), fun n => ?_⟩
    exact hs.le_tsum n (fun j _ => mul_nonneg (sq_nonneg _) (hnn j))
  obtain ⟨A, hA⟩ : ∃ A : ℝ,
      A = M * (k : ℝ) ^ (k - 1) / (Real.pi * (Nat.factorial (k - 2) : ℝ)) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (mul_nonneg hM0 (pow_nonneg (Nat.cast_nonneg _) _)) hF.le
  refine ⟨Real.sqrt A, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hP : ((n : ℝ) + k) ^ (k - 1) ≤ (k : ℝ) ^ (k - 1) * (((n : ℝ) + 1) ^ k) ^ 2 := by
    have h1 : (n : ℝ) + k ≤ k * ((n : ℝ) + 1) := by
      have := mul_nonneg hn0 (sub_nonneg.2 (show (1 : ℝ) ≤ k by linarith))
      nlinarith
    calc ((n : ℝ) + k) ^ (k - 1) ≤ ((k : ℝ) * ((n : ℝ) + 1)) ^ (k - 1) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = (k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1) := mul_pow _ _ _
      _ ≤ (k : ℝ) ^ (k - 1) * (((n : ℝ) + 1) ^ k) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← pow_mul]
          exact pow_le_pow_right₀ hn1 (by omega)
  have hx : ‖c n‖ ^ 2 * (Real.pi * (Nat.factorial (k - 2) : ℝ)) ≤
      M * ((n : ℝ) + k) ^ (k - 1) := by
    have h1 : ‖c n‖ ^ 2 * (Real.pi * (Nat.factorial (k - 2) : ℝ) / ((n : ℝ) + k) ^ (k - 1)) ≤
        M :=
      le_trans (mul_le_mul_of_nonneg_left (hmom n) (sq_nonneg _)) (hM n)
    rw [← mul_div_assoc, div_le_iff₀ (hnk n)] at h1
    exact h1
  have hx2 : ‖c n‖ ^ 2 ≤ A * (((n : ℝ) + 1) ^ k) ^ 2 := by
    rw [hA, div_mul_eq_mul_div, le_div_iff₀ hF]
    calc ‖c n‖ ^ 2 * (Real.pi * (Nat.factorial (k - 2) : ℝ)) ≤ M * ((n : ℝ) + k) ^ (k - 1) := hx
      _ ≤ M * ((k : ℝ) ^ (k - 1) * (((n : ℝ) + 1) ^ k) ^ 2) :=
          mul_le_mul_of_nonneg_left hP hM0
      _ = M * (k : ℝ) ^ (k - 1) * (((n : ℝ) + 1) ^ k) ^ 2 := by ring
  calc ‖c n‖ ≤ |‖c n‖| := le_abs_self _
    _ ≤ Real.sqrt (A * (((n : ℝ) + 1) ^ k) ^ 2) := Real.abs_le_sqrt hx2
    _ = Real.sqrt A * ((n : ℝ) + 1) ^ k := by
        rw [Real.sqrt_mul hA0, Real.sqrt_sq (by positivity)]

end Bound

/-! ### The reproducing formula -/

section Reproducing

variable {k : ℕ}

private lemma inv_conj_pow_eq {w : ℂ} (hw : w ≠ 0) (k : ℕ) :
    ((starRingEnd ℂ) w ^ k)⁻¹ = w ^ k * (((‖w‖ ^ 2) ^ k : ℝ) : ℂ)⁻¹ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hN : (((‖w‖ ^ 2) ^ k : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (pow_pos (pow_pos hn 2) k).ne'
  have hmul : w ^ k * (starRingEnd ℂ) w ^ k = (((‖w‖ ^ 2) ^ k : ℝ) : ℂ) := by
    rw [← mul_pow, Complex.mul_conj']
    norm_cast
  refine inv_eq_of_mul_eq_one_right ?_
  calc (starRingEnd ℂ) w ^ k * (w ^ k * (((‖w‖ ^ 2) ^ k : ℝ) : ℂ)⁻¹)
      = (w ^ k * (starRingEnd ℂ) w ^ k) * (((‖w‖ ^ 2) ^ k : ℝ) : ℂ)⁻¹ := by ring
    _ = 1 := by rw [hmul]; exact mul_inv_cancel₀ hN

private lemma reproducing_real {ζ : ℂ} (hζ : ‖ζ‖ < 1) (k : ℕ) :
    4 / (1 - ‖ζ‖ ^ 2) ^ 2 * (((‖icay ζ + I‖ ^ 2) ^ k)⁻¹ * (icay ζ).im ^ k) =
      (4 : ℝ) ^ (1 - (k : ℝ)) * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) := by
  have hs := one_sub_norm_sq_pos hζ
  have hd := norm_one_sub_pos hζ
  have hs' : 1 - ‖ζ‖ ^ 2 ≠ 0 := hs.ne'
  have hd' : ‖1 - ζ‖ ≠ 0 := hd.ne'
  have hw2 : (2 / ‖1 - ζ‖) ^ 2 = 4 / ‖1 - ζ‖ ^ 2 := by
    rw [div_pow]
    norm_num
  rw [norm_icay_add_I hζ, im_icay (ne_one_of_norm_lt_one hζ), rpow_sub_two hs k,
    four_rpow_one_sub, hw2]
  simp only [div_pow]
  field_simp

private lemma reproducing_pointwise {h : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ < 1) (k : ℕ) :
    (4 / (1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) •
        (((starRingEnd ℂ) (icay ζ + I) ^ k)⁻¹ * h (icay ζ) * (((icay ζ).im ^ k : ℝ) : ℂ)) =
      (4 : ℝ) ^ (1 - (k : ℝ)) • ((1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) • discTransform k h ζ) := by
  have hw := icay_add_I_ne_zero hζ
  have hreal := reproducing_real hζ k
  have hc : ((4 / (1 - ‖ζ‖ ^ 2) ^ 2 * (((‖icay ζ + I‖ ^ 2) ^ k)⁻¹ * (icay ζ).im ^ k) : ℝ) : ℂ) =
      (((4 : ℝ) ^ (1 - (k : ℝ)) * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) : ℝ) : ℂ) := by
    rw [hreal]
  simp only [Complex.real_smul, discTransform, smul_eq_mul, inv_conj_pow_eq hw]
  push_cast at hc ⊢
  linear_combination (((icay ζ + I) ^ k) * h (icay ζ)) * hc

private lemma integrableOn_weight {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ a) (Metric.ball 0 1) := by
  refine (integrableOn_moment 0 ha).congr_fun (fun ζ _ => ?_) Metric.isOpen_ball.measurableSet
  simp

private lemma integrableOn_disc_weight_smul (hk : 3 ≤ k) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h upper) {C : ℝ}
    (hC : ∀ z ∈ upper, ‖h z‖ * z.im ^ ((k : ℝ) / 2) ≤ C) :
    IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) • discTransform k h ζ)
      (Metric.ball 0 1) := by
  have hH := differentiableOn_discTransform (k := k) hh
  have ha : (-1 : ℝ) < (k : ℝ) / 2 - 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine Integrable.mono' (Integrable.const_mul (integrableOn_weight ha) ((2 : ℝ) ^ k * C)) ?_ ?_
  · exact ((continuousOn_weight _).smul hH.continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with ζ hζ
    have hζ' := mem_ball_zero_iff.1 hζ
    have hs := one_sub_norm_sq_pos hζ'
    have hA := norm_discTransform_mul_le hC hζ'
    have hsplit : (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) =
        (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2) * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2) := by
      rw [← Real.rpow_add hs]
      congr 1
      ring
    have hQ : 0 ≤ (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2) := Real.rpow_nonneg hs.le _
    show ‖(1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) • discTransform k h ζ‖ ≤
      (2 : ℝ) ^ k * C * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2)
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hs.le _)]
    calc (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) * ‖discTransform k h ζ‖
        = (‖discTransform k h ζ‖ * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2)) *
            (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2) := by rw [hsplit]; ring
      _ ≤ (2 ^ k * C) * (1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) / 2 - 2) :=
          mul_le_mul_of_nonneg_right hA hQ

/-- The weighted integrand of the reproducing formula is integrable. -/
theorem integrableOn_upper_reproducing (hk : 3 ≤ k) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h upper) {C : ℝ}
    (hC : ∀ z ∈ upper, ‖h z‖ * z.im ^ ((k : ℝ) / 2) ≤ C) :
    IntegrableOn (fun z => ((starRingEnd ℂ) (z + I) ^ k)⁻¹ * h z * ((z.im ^ k : ℝ) : ℂ)) upper
      hypMeasure := by
  rw [integrableOn_upper_iff]
  have hint : IntegrableOn
      (fun ζ : ℂ => (4 : ℝ) ^ (1 - (k : ℝ)) •
        ((1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) • discTransform k h ζ)) (Metric.ball 0 1) :=
    Integrable.smul ((4 : ℝ) ^ (1 - (k : ℝ))) (integrableOn_disc_weight_smul hk hh hC)
  refine IntegrableOn.congr_fun hint (fun ζ hζ => ?_) Metric.isOpen_ball.measurableSet
  exact (reproducing_pointwise (mem_ball_zero_iff.1 hζ) k).symm

/-- **The reproducing formula**: for `h` holomorphic with `‖h z‖ (Im z)^(k/2)` bounded,
`∫ conj(z + i)^(-k) h(z) (Im z)^k dμ = π/(k-1) 4^(1-k) (2i)^k h(i)`. -/
theorem integral_upper_reproducing (hk : 3 ≤ k) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h upper) {C : ℝ}
    (hC : ∀ z ∈ upper, ‖h z‖ * z.im ^ ((k : ℝ) / 2) ≤ C) :
    ∫ z in upper, ((starRingEnd ℂ) (z + I) ^ k)⁻¹ * h z * ((z.im ^ k : ℝ) : ℂ) ∂hypMeasure =
      ((Real.pi / ((k : ℝ) - 1) * (4 : ℝ) ^ (1 - (k : ℝ)) : ℝ) : ℂ) * (2 * I) ^ k * h I := by
  have hH := differentiableOn_discTransform (k := k) hh
  have ha : (-1 : ℝ) < (k : ℝ) - 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hint := integrableOn_disc_weight_smul hk hh hC
  have h1 : ∫ z in upper, ((starRingEnd ℂ) (z + I) ^ k)⁻¹ * h z * ((z.im ^ k : ℝ) : ℂ)
        ∂hypMeasure =
      ∫ ζ in Metric.ball (0 : ℂ) 1, (4 : ℝ) ^ (1 - (k : ℝ)) •
        ((1 - ‖ζ‖ ^ 2) ^ ((k : ℝ) - 2) • discTransform k h ζ) := by
    rw [integral_upper_eq_disc]
    exact setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      (fun ζ hζ => reproducing_pointwise (mem_ball_zero_iff.1 hζ) k)
  have hk1 : (k : ℝ) - 2 + 1 = (k : ℝ) - 1 := by ring
  rw [h1, integral_smul, integral_weight_smul_eq_complex hH ((k : ℝ) - 2) ha hint, discTransform_zero,
    hk1]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

end Reproducing

end TernaryPeriodPolynomials.Regularity

end
