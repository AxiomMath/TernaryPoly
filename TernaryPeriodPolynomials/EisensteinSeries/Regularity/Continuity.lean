module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Rotation

@[expose] public section


/-!
# Strong continuity of the Bergman representation

For `2 ≤ k` and a complex Hilbert space `E`, the representations `realRep` of `GL₂(ℝ)` and
`finRep` of `GL₂(𝔸_f)` on `BergmanSpace k E`, and hence `bergmanRep M` of `GL₂(𝔸)`, are strongly
continuous: every orbit map `x ↦ π x F` is continuous.

A map `f` into the Bergman space with `‖f x‖` constant is continuous as soon as all its
coefficient maps `x ↦ coeffPlus (f x) n`, `x ↦ coeffMinus (f x) n` are
(`continuous_of_continuous_coeff`): by Parseval the squared distance `‖f x - f x₀‖²` is the sum of
the weighted squared coefficient differences, the head of this series tends to `0`, and the tail
is controlled by `2 (‖f x‖² + ‖f x₀‖²)` together with the constancy of the norm.  The coefficients
of `realRep g F` are Cauchy integrals over the circle `|ζ| = 1/2` of an integrand jointly
continuous in `(g, ζ)`; those of `finRep u F` are `σ u` applied to the coefficients of `F`.
Continuity of `bergmanRep M` follows since both factors act isometrically.
-/

noncomputable section

open Filter Topology
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
  renaming realPart → svRealPart, finitePart → svFinitePart

namespace TernaryPeriodPolynomials.Regularity

namespace BergmanContinuity

section Abstract

/-- An isometric action with continuous orbit maps is jointly continuous in the group element
and the vector. -/
theorem continuous_uncurry_of_isometry {Y H : Type*} [TopologicalSpace Y] [PseudoMetricSpace H]
    {T : Y → H → H} (hiso : ∀ y G G', dist (T y G) (T y G') = dist G G')
    (hcont : ∀ G, Continuous fun y => T y G) : Continuous fun p : Y × H => T p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨y₀, G₀⟩
  have h1 : Tendsto (fun p : Y × H => dist p.2 G₀) (𝓝 (y₀, G₀)) (𝓝 0) := by
    have hc : Continuous fun _ : Y × H => G₀ := continuous_const
    simpa using (continuous_snd.dist hc).tendsto (y₀, G₀)
  have h2 : Tendsto (fun p : Y × H => dist (T p.1 G₀) (T y₀ G₀)) (𝓝 (y₀, G₀)) (𝓝 0) := by
    have hc : Continuous fun _ : Y × H => T y₀ G₀ := continuous_const
    simpa using (((hcont G₀).comp continuous_fst).dist hc).tendsto (y₀, G₀)
  have h3 : Tendsto (fun p : Y × H => dist p.2 G₀ + dist (T p.1 G₀) (T y₀ G₀)) (𝓝 (y₀, G₀))
      (𝓝 0) := by
    simpa using h1.add h2
  have key : Tendsto (fun p : Y × H => dist (T p.1 p.2) (T y₀ G₀)) (𝓝 (y₀, G₀)) (𝓝 0) := by
    refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) h3
    calc dist (T p.1 p.2) (T y₀ G₀)
        ≤ dist (T p.1 p.2) (T p.1 G₀) + dist (T p.1 G₀) (T y₀ G₀) := dist_triangle _ _ _
      _ = dist p.2 G₀ + dist (T p.1 G₀) (T y₀ G₀) := by rw [hiso]
  exact tendsto_iff_dist_tendsto_zero.2 key

/-- Squared distances of sequences of series with uniformly small tails tend to `0`: if `a · x`
sums to the constant `c`, `d · x` sums to `D x`, `d · x₀` vanishes, and `d ≤ 2 (a x + a x₀)`, then
`D` tends to `0` at `x₀`. -/
theorem tendsto_zero_of_tail {X : Type*} [TopologicalSpace X] {x₀ : X} {a d : ℕ → X → ℝ}
    {c : ℝ} {D : X → ℝ} (ha : ∀ x, HasSum (fun n => a n x) c)
    (hd : ∀ x, HasSum (fun n => d n x) (D x)) (hac : ∀ n, Continuous (a n))
    (hdc : ∀ n, Continuous (d n)) (hd0 : ∀ n, d n x₀ = 0) (hdnn : ∀ n x, 0 ≤ d n x)
    (hbound : ∀ n x, d n x ≤ 2 * (a n x + a n x₀)) : Tendsto D (𝓝 x₀) (𝓝 0) := by
  have hD0 : ∀ x, 0 ≤ D x := fun x => (hd x).nonneg fun n => hdnn n x
  refine tendsto_order.2 ⟨fun r hr => Filter.Eventually.of_forall fun x =>
    lt_of_lt_of_le hr (hD0 x), fun r hr => ?_⟩
  obtain ⟨ε, hε0, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ 5 * ε = r := ⟨r / 5, by linarith, by ring⟩
  have hpart : Tendsto (fun n => ∑ i ∈ Finset.range n, a i x₀) atTop (𝓝 c) :=
    (ha x₀).tendsto_sum_nat
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hpart).1 (c - ε) (by linarith)).exists
  have hN' : c - ε < ∑ i ∈ Finset.range N, a i x₀ := hN
  have hA : Tendsto (fun x => ∑ i ∈ Finset.range N, a i x) (𝓝 x₀)
      (𝓝 (∑ i ∈ Finset.range N, a i x₀)) :=
    (continuous_finsetSum (Finset.range N) fun i _ => hac i).tendsto x₀
  have hDh : Tendsto (fun x => ∑ i ∈ Finset.range N, d i x) (𝓝 x₀) (𝓝 0) := by
    have h := (continuous_finsetSum (Finset.range N) fun i _ => hdc i).tendsto x₀
    have h0 : ∑ i ∈ Finset.range N, d i x₀ = 0 := Finset.sum_eq_zero fun i _ => hd0 i
    rw [h0] at h
    exact h
  filter_upwards [(tendsto_order.1 hA).1 (c - ε) hN', (tendsto_order.1 hDh).2 ε hε0] with x hx1 hx2
  have hx1' : c - ε < ∑ i ∈ Finset.range N, a i x := hx1
  have hx2' : ∑ i ∈ Finset.range N, d i x < ε := hx2
  have e1 : HasSum (fun n => d (n + N) x) (D x - ∑ i ∈ Finset.range N, d i x) :=
    (hasSum_nat_add_iff' N).2 (hd x)
  have e2 : HasSum (fun n => a (n + N) x) (c - ∑ i ∈ Finset.range N, a i x) :=
    (hasSum_nat_add_iff' N).2 (ha x)
  have e3 : HasSum (fun n => a (n + N) x₀) (c - ∑ i ∈ Finset.range N, a i x₀) :=
    (hasSum_nat_add_iff' N).2 (ha x₀)
  have e4 := hasSum_le (fun n => hbound (n + N) x) e1 ((e2.add e3).mul_left 2)
  linarith

end Abstract

section Bergman

theorem norm_sub_sq_le {E : Type*} [NormedAddCommGroup E] (u v : E) :
    ‖u - v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg (u - v)) (norm_sub_le u v) 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem coeffPlus_sub {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F G : BergmanSpace k E) (n : ℕ) :
    coeffPlus (F - G) n = coeffPlus F n - coeffPlus G n := by
  have h := coeffPlus_add (F - G) G n
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem coeffMinus_sub {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F G : BergmanSpace k E) (n : ℕ) :
    coeffMinus (F - G) n = coeffMinus F n - coeffMinus G n := by
  have h := coeffMinus_add (F - G) G n
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- A map into the Bergman space with constant norm is continuous if all its coefficient maps
are. -/
theorem continuous_of_continuous_coeff {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (hk : 2 ≤ k) {X : Type*} [TopologicalSpace X]
    {f : X → BergmanSpace k E} {c : ℝ} (hn : ∀ x, ‖f x‖ = c)
    (hP : ∀ n, Continuous fun x => coeffPlus (f x) n)
    (hM : ∀ n, Continuous fun x => coeffMinus (f x) n) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hD : Tendsto (fun x => ‖f x - f x₀‖ ^ 2) (𝓝 x₀) (𝓝 0) := by
    refine tendsto_zero_of_tail
      (a := fun n x => bergmanWeight k n * (‖coeffPlus (f x) n‖ ^ 2 + ‖coeffMinus (f x) n‖ ^ 2))
      (d := fun n x => bergmanWeight k n * (‖coeffPlus (f x) n - coeffPlus (f x₀) n‖ ^ 2 +
        ‖coeffMinus (f x) n - coeffMinus (f x₀) n‖ ^ 2))
      (c := c ^ 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x
      have h := hasSum_norm_sq hk (f x)
      rw [hn x] at h
      exact h
    · intro x
      have h := hasSum_norm_sq hk (f x - f x₀)
      simp only [coeffPlus_sub, coeffMinus_sub] at h
      exact h
    · intro n
      exact continuous_const.mul (((hP n).norm.pow 2).add ((hM n).norm.pow 2))
    · intro n
      have hP' : Continuous fun x => coeffPlus (f x) n - coeffPlus (f x₀) n :=
        (hP n).sub continuous_const
      have hM' : Continuous fun x => coeffMinus (f x) n - coeffMinus (f x₀) n :=
        (hM n).sub continuous_const
      exact continuous_const.mul ((hP'.norm.pow 2).add (hM'.norm.pow 2))
    · intro n
      simp
    · intro n x
      exact mul_nonneg (bergmanWeight_pos hk n).le (add_nonneg (sq_nonneg _) (sq_nonneg _))
    · intro n x
      have hw := (bergmanWeight_pos hk n).le
      have h1 := norm_sub_sq_le (coeffPlus (f x) n) (coeffPlus (f x₀) n)
      have h2 := norm_sub_sq_le (coeffMinus (f x) n) (coeffMinus (f x₀) n)
      have key := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hw
      show bergmanWeight k n * (‖coeffPlus (f x) n - coeffPlus (f x₀) n‖ ^ 2 +
          ‖coeffMinus (f x) n - coeffMinus (f x₀) n‖ ^ 2) ≤
        2 * (bergmanWeight k n * (‖coeffPlus (f x) n‖ ^ 2 + ‖coeffMinus (f x) n‖ ^ 2) +
          bergmanWeight k n * (‖coeffPlus (f x₀) n‖ ^ 2 + ‖coeffMinus (f x₀) n‖ ^ 2))
      linarith
  have hsq := (Real.continuous_sqrt.tendsto 0).comp hD
  rw [Real.sqrt_zero] at hsq
  show Tendsto f (𝓝 x₀) (𝓝 (f x₀))
  refine tendsto_iff_dist_tendsto_zero.2 (hsq.congr fun x => ?_)
  show Real.sqrt (‖f x - f x₀‖ ^ 2) = dist (f x) (f x₀)
  rw [Real.sqrt_sq (norm_nonneg _), dist_eq_norm]

end Bergman

section Matrices

variable {X : Type*} [TopologicalSpace X]

theorem continuous_val_apply {g : X → GL (Fin 2) ℝ} (hg : Continuous g) (i j : Fin 2) :
    Continuous fun x => (g x).val i j :=
  (Units.continuous_val.comp hg).matrix_elem i j

theorem continuous_inv_val_apply {g : X → GL (Fin 2) ℝ} (hg : Continuous g) (i j : Fin 2) :
    Continuous fun x => ((g x)⁻¹).val i j :=
  ((Units.continuous_iff.1 hg).2).matrix_elem i j

theorem continuous_det_val {g : X → GL (Fin 2) ℝ} (hg : Continuous g) :
    Continuous fun x => (g x).val.det := by
  have h : Continuous fun x => (g x).val 0 0 * (g x).val 1 1 - (g x).val 0 1 * (g x).val 1 0 :=
    ((continuous_val_apply hg 0 0).mul (continuous_val_apply hg 1 1)).sub
      ((continuous_val_apply hg 0 1).mul (continuous_val_apply hg 1 0))
  exact h.congr fun x => (gl_det_eq (g x)).symm

theorem continuous_denom_inv {g : X → GL (Fin 2) ℝ} (hg : Continuous g) {w : X → ℂ}
    (hw : Continuous w) : Continuous fun x => denom (g x)⁻¹ (w x) := by
  have h10 : Continuous fun x => ((((g x)⁻¹).val 1 0 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inv_val_apply hg 1 0)
  have h11 : Continuous fun x => ((((g x)⁻¹).val 1 1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inv_val_apply hg 1 1)
  exact (h10.mul hw).add h11

theorem continuous_moeb_inv {g : X → GL (Fin 2) ℝ} (hg : Continuous g) {w : X → ℂ}
    (hw : Continuous w) (hne : ∀ x, (w x).im ≠ 0) : Continuous fun x => moeb (g x)⁻¹ (w x) := by
  have h00 : Continuous fun x => ((((g x)⁻¹).val 0 0 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inv_val_apply hg 0 0)
  have h01 : Continuous fun x => ((((g x)⁻¹).val 0 1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inv_val_apply hg 0 1)
  have hN : Continuous fun x => ((((g x)⁻¹).val 0 0 : ℝ) : ℂ) * w x +
      ((((g x)⁻¹).val 0 1 : ℝ) : ℂ) := (h00.mul hw).add h01
  exact hN.div (continuous_denom_inv hg hw) fun x => denom_ne_zero _ (hne x)

theorem continuous_autFactor_comp (k : ℕ) {g : X → GL (Fin 2) ℝ} (hg : Continuous g)
    {w : X → ℂ} (hw : Continuous w) (hne : ∀ x, (w x).im ≠ 0) :
    Continuous fun x => autFactor k (g x) (w x) := by
  have hdet : Continuous fun x => |(g x).val.det| := continuous_abs.comp (continuous_det_val hg)
  have hpow : Continuous fun x => |(g x).val.det| ^ ((k : ℝ) / 2) :=
    hdet.rpow_const fun x => Or.inr (by positivity)
  have hinv : Continuous fun x => (|(g x).val.det| ^ ((k : ℝ) / 2))⁻¹ :=
    hpow.inv₀ fun x => (Real.rpow_pos_of_pos (abs_pos.2 (gl_det_ne_zero (g x))) _).ne'
  have hD : Continuous fun x => denom (g x)⁻¹ (w x) ^ k :=
    (continuous_denom_inv hg hw).pow k
  have hD' : Continuous fun x => (denom (g x)⁻¹ (w x) ^ k)⁻¹ :=
    hD.inv₀ fun x => pow_ne_zero _ (denom_ne_zero _ (hne x))
  have hr : Continuous fun x => (((|(g x).val.det| ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hinv
  exact hr.mul hD'

end Matrices

section Real

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem continuous_realRep_apply {X : Type*} [TopologicalSpace X] (F : BergmanSpace k E)
    {g : X → GL (Fin 2) ℝ} (hg : Continuous g) {w : X → ℂ} (hw : Continuous w)
    (hne : ∀ x, (w x).im ≠ 0) : Continuous fun x => realRep k E (g x) F (w x) := by
  have hm : Continuous fun x => moeb (g x)⁻¹ (w x) := continuous_moeb_inv hg hw hne
  have hF : Continuous fun x => F (moeb (g x)⁻¹ (w x)) :=
    F.continuousOn.comp_continuous hm fun x => moeb_mem_offReal _ (mem_offReal_iff.2 (hne x))
  have h : Continuous fun x => autFactor k (g x) (w x) • F (moeb (g x)⁻¹ (w x)) :=
    (continuous_autFactor_comp k hg hw hne).smul hF
  exact h.congr fun x => (realRep_apply (g x) F (hne x)).symm

theorem dist_realRep (r : GL (Fin 2) ℝ) (G G' : BergmanSpace k E) :
    dist (realRep k E r G) (realRep k E r G') = dist G G' := by
  have h : realRep k E r G - realRep k E r G' = realRep k E r (G - G') :=
    (map_sub (realRep k E r) G G').symm
  rw [dist_eq_norm, dist_eq_norm, h, norm_realRep]

theorem continuous_icay_comp {X : Type*} [TopologicalSpace X] {u : X → ℂ} (hu : Continuous u)
    (h : ∀ x, 1 - u x ≠ 0) : Continuous fun x => icay (u x) := by
  have hI : Continuous fun _ : X => Complex.I := continuous_const
  have h1 : Continuous fun _ : X => (1 : ℂ) := continuous_const
  have hN : Continuous fun x => Complex.I * (1 + u x) := hI.mul (h1.add hu)
  have hd : Continuous fun x => 1 - u x := h1.sub hu
  exact hN.div hd h

theorem norm_circleMap_half (θ : ℝ) : ‖circleMap 0 (1 / 2) θ‖ = 1 / 2 := by
  rw [norm_circleMap_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

theorem norm_circleMap_half_lt_one (θ : ℝ) : ‖circleMap 0 (1 / 2) θ‖ < 1 := by
  rw [norm_circleMap_half]
  norm_num

theorem one_sub_circleMap_half_ne_zero (θ : ℝ) : 1 - circleMap 0 (1 / 2) θ ≠ 0 := by
  intro h
  have h1 : circleMap 0 (1 / 2) θ = 1 := (sub_eq_zero.1 h).symm
  have h2 := norm_circleMap_half θ
  rw [h1, norm_one] at h2
  norm_num at h2

theorem im_icay_circleMap_half_pos (θ : ℝ) : 0 < (icay (circleMap 0 (1 / 2) θ)).im :=
  mem_upper_iff.1 (icay_mem_upper (norm_circleMap_half_lt_one θ))

theorem continuous_icay_circleMap_half : Continuous fun θ : ℝ => icay (circleMap 0 (1 / 2) θ) :=
  continuous_icay_comp (continuous_circleMap 0 (1 / 2)) one_sub_circleMap_half_ne_zero

/-- The integrand of the Cauchy integral for `coeffPlus (realRep g F) n` is jointly continuous in
`(g, θ)`. -/
theorem continuous_circle_plus (F : BergmanSpace k E) :
    Continuous fun p : GL (Fin 2) ℝ × ℝ =>
      discTransform k (⇑(realRep k E p.1 F)) (circleMap 0 (1 / 2) p.2) := by
  have hw : Continuous fun p : GL (Fin 2) ℝ × ℝ => icay (circleMap 0 (1 / 2) p.2) :=
    continuous_icay_circleMap_half.comp continuous_snd
  have hne : ∀ p : GL (Fin 2) ℝ × ℝ, (icay (circleMap 0 (1 / 2) p.2)).im ≠ 0 :=
    fun p => (im_icay_circleMap_half_pos p.2).ne'
  have hI : Continuous fun _ : GL (Fin 2) ℝ × ℝ => Complex.I := continuous_const
  have hs : Continuous fun p : GL (Fin 2) ℝ × ℝ =>
      (icay (circleMap 0 (1 / 2) p.2) + Complex.I) ^ k := (hw.add hI).pow k
  have hr : Continuous fun p : GL (Fin 2) ℝ × ℝ =>
      realRep k E p.1 F (icay (circleMap 0 (1 / 2) p.2)) :=
    continuous_realRep_apply F continuous_fst hw hne
  exact hs.smul hr

/-- The integrand of the Cauchy integral for `coeffMinus (realRep g F) n` is jointly continuous
in `(g, θ)`. -/
theorem continuous_circle_minus (F : BergmanSpace k E) :
    Continuous fun p : GL (Fin 2) ℝ × ℝ =>
      discTransform k (lowerPart ⇑(realRep k E p.1 F)) (circleMap 0 (1 / 2) p.2) := by
  have hw : Continuous fun p : GL (Fin 2) ℝ × ℝ => icay (circleMap 0 (1 / 2) p.2) :=
    continuous_icay_circleMap_half.comp continuous_snd
  have hwn : Continuous fun p : GL (Fin 2) ℝ × ℝ => -icay (circleMap 0 (1 / 2) p.2) := hw.neg
  have hne : ∀ p : GL (Fin 2) ℝ × ℝ, (-icay (circleMap 0 (1 / 2) p.2)).im ≠ 0 := fun p => by
    rw [Complex.neg_im]
    exact neg_ne_zero.2 (im_icay_circleMap_half_pos p.2).ne'
  have hI : Continuous fun _ : GL (Fin 2) ℝ × ℝ => Complex.I := continuous_const
  have hs : Continuous fun p : GL (Fin 2) ℝ × ℝ =>
      (icay (circleMap 0 (1 / 2) p.2) + Complex.I) ^ k := (hw.add hI).pow k
  have hr : Continuous fun p : GL (Fin 2) ℝ × ℝ =>
      realRep k E p.1 F (-icay (circleMap 0 (1 / 2) p.2)) :=
    continuous_realRep_apply F continuous_fst hwn hne
  exact hs.smul hr

end Real

section Taylor

/-- A circle integral with a jointly continuous integrand depends continuously on a parameter. -/
theorem continuous_circleIntegral_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {X : Type*} [TopologicalSpace X] (K : X → ℂ → E) (R : ℝ)
    (hK : Continuous fun p : X × ℝ => K p.1 (circleMap 0 R p.2)) :
    Continuous fun x => circleIntegral (K x) 0 R := by
  have hI : Continuous fun _ : X × ℝ => Complex.I := continuous_const
  have hd : Continuous fun p : X × ℝ => deriv (circleMap 0 R) p.2 := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul hI
  have h : Continuous (Function.uncurry fun (x : X) (θ : ℝ) =>
      deriv (circleMap 0 R) θ • K x (circleMap 0 R θ)) := hd.smul hK
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 (2 * Real.pi)

/-- The Taylor coefficients of functions on the unit disc depend continuously on a parameter if
the functions are jointly continuous on the circle of radius `1/2`. -/
theorem continuous_taylorCoeff_of_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {X : Type*} [TopologicalSpace X] (H : X → ℂ → E) (n : ℕ)
    (hH : Continuous fun p : X × ℝ => H p.1 (circleMap 0 (1 / 2) p.2)) :
    Continuous fun x => taylorCoeff (H x) n := by
  have hc : Continuous fun p : X × ℝ => circleMap 0 (1 / 2) p.2 :=
    (continuous_circleMap 0 (1 / 2)).comp continuous_snd
  have hne : ∀ p : X × ℝ, circleMap 0 (1 / 2) p.2 - 0 ≠ 0 := fun p => by
    rw [sub_zero]
    exact circleMap_ne_center (by norm_num)
  have h0 : Continuous fun _ : X × ℝ => (0 : ℂ) := continuous_const
  have h1 : Continuous fun _ : X × ℝ => (1 : ℂ) := continuous_const
  have hz : Continuous fun p : X × ℝ => circleMap 0 (1 / 2) p.2 - 0 := hc.sub h0
  have hz1 : Continuous fun p : X × ℝ => 1 / (circleMap 0 (1 / 2) p.2 - 0) := h1.div hz hne
  have hz2 : Continuous fun p : X × ℝ => (circleMap 0 (1 / 2) p.2 - 0)⁻¹ := hz.inv₀ hne
  have hK : Continuous fun p : X × ℝ =>
      (1 / (circleMap 0 (1 / 2) p.2 - 0)) ^ n •
        (circleMap 0 (1 / 2) p.2 - 0)⁻¹ • H p.1 (circleMap 0 (1 / 2) p.2) :=
    (hz1.pow n).smul (hz2.smul hH)
  have e : (fun x => taylorCoeff (H x) n) = fun x =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • circleIntegral
        (fun z => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • H x z) 0 (1 / 2) :=
    funext fun x => by
      unfold taylorCoeff
      exact cauchyPowerSeries_apply (H x) 0 (1 / 2) n 1
  rw [e]
  exact (continuous_circleIntegral_param
    (fun x z => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • H x z) (1 / 2) hK).const_smul _

end Taylor

section Coefficients

theorem continuous_coeffPlus_realRep {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (F : BergmanSpace k E) (n : ℕ) :
    Continuous fun g : GL (Fin 2) ℝ => coeffPlus (realRep k E g F) n :=
  continuous_taylorCoeff_of_circle (fun g ζ => discTransform k (⇑(realRep k E g F)) ζ) n
    (continuous_circle_plus F)

theorem continuous_coeffMinus_realRep {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (F : BergmanSpace k E) (n : ℕ) :
    Continuous fun g : GL (Fin 2) ℝ => coeffMinus (realRep k E g F) n :=
  continuous_taylorCoeff_of_circle
    (fun g ζ => discTransform k (lowerPart ⇑(realRep k E g F)) ζ) n (continuous_circle_minus F)

end Coefficients

section Components

theorem continuous_realPart : Continuous (svRealPart : BinaryAdelicGL → BinaryRealGL) := by
  unfold svRealPart
  apply Units.continuous_map
  exact continuous_pi fun i => continuous_pi fun j =>
    continuous_fst.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_finitePart : Continuous (svFinitePart : BinaryAdelicGL → BinaryFiniteGL) := by
  unfold svFinitePart
  apply Units.continuous_map
  exact continuous_pi fun i => continuous_pi fun j =>
    continuous_snd.comp ((continuous_apply j).comp (continuous_apply i))

end Components

end BergmanContinuity

/-- The orbit maps of `realRep` are continuous. -/
theorem continuous_realRep {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (hk : 2 ≤ k) (F : BergmanSpace k E) :
    Continuous fun g : GL (Fin 2) ℝ => realRep k E g F :=
  BergmanContinuity.continuous_of_continuous_coeff hk (f := fun g => realRep k E g F) (c := ‖F‖)
    (fun g => norm_realRep g F) (BergmanContinuity.continuous_coeffPlus_realRep F)
    (BergmanContinuity.continuous_coeffMinus_realRep F)

/-- The orbit maps of `finRep` are continuous when the underlying representation is strongly
continuous. -/
theorem continuous_finRep {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (hk : 2 ≤ k) (σ : Representation ℂ BinaryFiniteGL E)
    (hσ : ∀ g e, ‖σ g e‖ = ‖e‖) (hσc : ∀ e, Continuous fun g => σ g e) (F : BergmanSpace k E) :
    Continuous fun u : BinaryFiniteGL => finRep k σ hσ u F :=
  BergmanContinuity.continuous_of_continuous_coeff hk (f := fun u => finRep k σ hσ u F)
    (c := ‖F‖) (fun u => norm_finRep σ hσ u F)
    (fun n => (hσc (coeffPlus F n)).congr fun u => (coeffPlus_finRep σ hσ u F n).symm)
    (fun n => (hσc (coeffMinus F n)).congr fun u => (coeffMinus_finRep σ hσ u F n).symm)

/-- **Strong continuity** of the unitary representation `bergmanRep M` of `GL₂(𝔸)`. -/
theorem continuous_bergmanRep {k : ℕ} (hk : 2 ≤ k) (M : FiniteModel k) (F : BergmanSpace k M.E) :
    Continuous fun x : BinaryAdelicGL => bergmanRep M x F := by
  have hfin : Continuous fun x : BinaryAdelicGL => finRep k M.σ M.unitary (svFinitePart x) F :=
    (continuous_finRep hk M.σ M.unitary M.continuous F).comp BergmanContinuity.continuous_finitePart
  have hjoint : Continuous fun p : GL (Fin 2) ℝ × BergmanSpace k M.E => realRep k M.E p.1 p.2 :=
    BergmanContinuity.continuous_uncurry_of_isometry
      (T := fun (r : GL (Fin 2) ℝ) (G : BergmanSpace k M.E) => realRep k M.E r G)
      (fun r G G' => BergmanContinuity.dist_realRep r G G') (fun G => continuous_realRep hk G)
  have hpair : Continuous fun x : BinaryAdelicGL =>
      (svRealPart x, finRep k M.σ M.unitary (svFinitePart x) F) :=
    BergmanContinuity.continuous_realPart.prodMk hfin
  have hcomp := hjoint.comp hpair
  refine hcomp.congr fun x => ?_
  exact (bergmanRep_apply M x F).symm

end TernaryPeriodPolynomials.Regularity

end
