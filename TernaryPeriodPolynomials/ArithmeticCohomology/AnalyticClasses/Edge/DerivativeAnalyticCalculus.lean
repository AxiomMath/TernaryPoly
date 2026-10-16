module

public import Mathlib

@[expose] public section


/-!
# Differentiation under the integral for uniformly Lipschitz families

A family `f i` of complex functions on a set `B` of a normed space is *uniformly Lipschitz* if
all `f i` are bounded on `B` and Lipschitz on `B` with one common constant. If a parametric
integrand is `T(u) · f u p` with `‖T‖` integrable and `f` uniformly Lipschitz on a neighbourhood of
`p₀`, and each `p ↦ f u p` is differentiable at `p₀`, then the integral is differentiable at `p₀`
with derivative the integral of the derivatives. The derivatives are measurable as limits of
difference quotients. A jointly `C¹` function on a neighbourhood of `K × B`, with `K` compact and
`B` compact convex, gives a uniformly Lipschitz family indexed by `K`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Measurability of derivatives -/

/-- A derivative of a family of measurable functions is measurable. -/
theorem aestronglyMeasurable_of_hasDerivAt {f : ℝ → α → E} {f' : α → E} {x₀ : ℝ}
    (measurable : ∀ x, AEStronglyMeasurable (f x) μ)
    (derivative : ∀ᵐ a ∂μ, HasDerivAt (fun x => f x a) (f' a) x₀) :
    AEStronglyMeasurable f' μ := by
  set x : ℕ → ℝ := fun k => x₀ + 1 / ((k : ℝ) + 1)
  have approach : Tendsto x atTop (𝓝[≠] x₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun k => ?_)
    · simpa [x] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add x₀
    · change x₀ + 1 / ((k : ℝ) + 1) ≠ x₀
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun k a => (x k - x₀)⁻¹ • (f (x k) a - f x₀ a)) (fun k => ?_) ?_
  · exact ((measurable (x k)).sub (measurable x₀)).const_smul _
  · filter_upwards [derivative] with a ha
    have := (hasDerivAt_iff_tendsto_slope.mp ha).comp approach
    simpa only [Function.comp_def, slope_def_module] using this

/-- A Fréchet derivative of a family of measurable functions on a finite-dimensional space is
measurable. -/
theorem aestronglyMeasurable_of_hasFDerivAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {f : P → α → E} {f' : α → P →L[ℝ] E} {x₀ : P}
    (measurable : ∀ x, AEStronglyMeasurable (f x) μ)
    (derivative : ∀ᵐ a ∂μ, HasFDerivAt (fun x => f x a) (f' a) x₀) :
    AEStronglyMeasurable f' μ := by
  set b := Module.finBasis ℝ P
  set coordinate : Fin (Module.finrank ℝ P) → P →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have expansion (L : P →L[ℝ] E) : L = ∑ i, (coordinate i).smulRight (L (b i)) := by
    ext v
    rw [_root_.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply, coordinate,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul]
  have component (i : Fin (Module.finrank ℝ P)) :
      AEStronglyMeasurable (fun a => f' a (b i)) μ := by
    refine aestronglyMeasurable_of_hasDerivAt (f := fun t a => f (x₀ + t • b i) a) (x₀ := 0)
      (fun t => measurable _) ?_
    filter_upwards [derivative] with a ha
    have line : HasDerivAt (fun t : ℝ => x₀ + t • b i) (b i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (b i)).const_add x₀
    have outer : HasFDerivAt (fun x => f x a) (f' a) (x₀ + (0 : ℝ) • b i) := by
      simpa using ha
    exact outer.comp_hasDerivAt (0 : ℝ) line
  have sum : AEStronglyMeasurable
      (fun a => ∑ i, (coordinate i).smulRight (f' a (b i))) μ := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ P E (coordinate i)).continuous.comp_aestronglyMeasurable
      (component i)
  refine sum.congr (Eventually.of_forall fun a => ?_)
  exact (expansion (f' a)).symm

/-! ### Uniformly Lipschitz families -/

/-- A family of complex functions on `B`, bounded and Lipschitz on `B` with one constant. -/
def UniformLipOn {ι P : Type*} [NormedAddCommGroup P] (f : ι → P → ℂ) (B : Set P) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ p ∈ B, ‖f i p‖ ≤ C ∧ ∀ q ∈ B, ‖f i p - f i q‖ ≤ C * ‖p - q‖

namespace UniformLipOn

variable {ι P : Type*} [NormedAddCommGroup P] {B : Set P}

theorem const {c : ι → ℂ} {D : ℝ} (bound : ∀ i, ‖c i‖ ≤ D) :
    UniformLipOn (fun i (_ : P) => c i) B := by
  refine ⟨max D 0, le_max_right _ _, fun i p _ => ⟨(bound i).trans (le_max_left _ _),
    fun q _ => ?_⟩⟩
  rw [sub_self, norm_zero]
  exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

theorem zero : UniformLipOn (fun (_ : ι) (_ : P) => (0 : ℂ)) B :=
  const (D := 0) fun _ => by simp

theorem mono {f : ι → P → ℂ} {B' : Set P} (hf : UniformLipOn f B) (sub : B' ⊆ B) :
    UniformLipOn f B' := by
  obtain ⟨C, hC0, hC⟩ := hf
  exact ⟨C, hC0, fun i p hp => ⟨(hC i p (sub hp)).1, fun q hq => (hC i p (sub hp)).2 q (sub hq)⟩⟩

theorem congr {f g : ι → P → ℂ} (hf : UniformLipOn f B) (equal : ∀ i, ∀ p ∈ B, f i p = g i p) :
    UniformLipOn g B := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨C, hC0, fun i p hp => ⟨?_, fun q hq => ?_⟩⟩
  · rw [← equal i p hp]
    exact (hC i p hp).1
  · rw [← equal i p hp, ← equal i q hq]
    exact (hC i p hp).2 q hq

theorem add {f g : ι → P → ℂ} (hf : UniformLipOn f B) (hg : UniformLipOn g B) :
    UniformLipOn (fun i p => f i p + g i p) B := by
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨D, hD0, hD⟩ := hg
  refine ⟨C + D, add_nonneg hC0 hD0, fun i p hp => ⟨?_, fun q hq => ?_⟩⟩
  · exact (norm_add_le _ _).trans (add_le_add (hC i p hp).1 (hD i p hp).1)
  · calc ‖f i p + g i p - (f i q + g i q)‖ = ‖(f i p - f i q) + (g i p - g i q)‖ := by
          congr 1; ring
      _ ≤ C * ‖p - q‖ + D * ‖p - q‖ :=
          (norm_add_le _ _).trans (add_le_add ((hC i p hp).2 q hq) ((hD i p hp).2 q hq))
      _ = (C + D) * ‖p - q‖ := by ring

theorem neg {f : ι → P → ℂ} (hf : UniformLipOn f B) : UniformLipOn (fun i p => -f i p) B := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨C, hC0, fun i p hp => ⟨by rw [norm_neg]; exact (hC i p hp).1, fun q hq => ?_⟩⟩
  rw [show -f i p - -f i q = -(f i p - f i q) by ring, norm_neg]
  exact (hC i p hp).2 q hq

theorem sub {f g : ι → P → ℂ} (hf : UniformLipOn f B) (hg : UniformLipOn g B) :
    UniformLipOn (fun i p => f i p - g i p) B :=
  (hf.add hg.neg).congr fun _ _ _ => (sub_eq_add_neg _ _).symm

theorem mul {f g : ι → P → ℂ} (hf : UniformLipOn f B) (hg : UniformLipOn g B) :
    UniformLipOn (fun i p => f i p * g i p) B := by
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨D, hD0, hD⟩ := hg
  refine ⟨C * D + (C * D + D * C), by positivity, fun i p hp => ⟨?_, fun q hq => ?_⟩⟩
  · rw [norm_mul]
    calc ‖f i p‖ * ‖g i p‖ ≤ C * D :=
          mul_le_mul (hC i p hp).1 (hD i p hp).1 (norm_nonneg _) hC0
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · calc ‖f i p * g i p - f i q * g i q‖ =
        ‖f i p * (g i p - g i q) + g i q * (f i p - f i q)‖ := by congr 1; ring
      _ ≤ C * (D * ‖p - q‖) + D * (C * ‖p - q‖) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul (hC i p hp).1 ((hD i p hp).2 q hq) (norm_nonneg _) hC0
          · exact mul_le_mul (hD i q hq).1 ((hC i p hp).2 q hq) (norm_nonneg _) hD0
      _ ≤ (C * D + (C * D + D * C)) * ‖p - q‖ := by
          have := norm_nonneg (p - q)
          nlinarith [mul_nonneg (mul_nonneg hC0 hD0) this]

theorem sum {κ : Type*} (s : Finset κ) {f : κ → ι → P → ℂ}
    (hf : ∀ k ∈ s, UniformLipOn (f k) B) : UniformLipOn (fun i p => ∑ k ∈ s, f k i p) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : UniformLipOn (fun (_ : ι) (_ : P) => (0 : ℂ)) B)
  | insert k s hk induction =>
    have first := hf k (Finset.mem_insert_self k s)
    have rest := induction fun k' hk' => hf k' (Finset.mem_insert_of_mem hk')
    exact (first.add rest).congr fun i p _ => by rw [Finset.sum_insert hk]

/-- A uniformly Lipschitz family of functions with values in a set `K`, followed by a uniformly
Lipschitz family of functions on `K`. -/
theorem comp {κ : Type*} {z : ι → P → ℂ} {g : κ → ℂ → ℂ} {K : Set ℂ} {index : ι → κ}
    (hz : UniformLipOn z B) (maps : ∀ i, ∀ p ∈ B, z i p ∈ K)
    (hg : ∃ D : ℝ, 0 ≤ D ∧ ∀ k, ∀ w ∈ K, ‖g k w‖ ≤ D ∧ ∀ w' ∈ K, ‖g k w - g k w'‖ ≤ D * ‖w - w'‖) :
    UniformLipOn (fun i p => g (index i) (z i p)) B := by
  obtain ⟨C, hC0, hC⟩ := hz
  obtain ⟨D, hD0, hD⟩ := hg
  refine ⟨D + D * C, by positivity, fun i p hp => ⟨?_, fun q hq => ?_⟩⟩
  · exact (hD _ _ (maps i p hp)).1.trans (le_add_of_nonneg_right (by positivity))
  · calc ‖g (index i) (z i p) - g (index i) (z i q)‖ ≤ D * ‖z i p - z i q‖ :=
          (hD _ _ (maps i p hp)).2 _ (maps i q hq)
      _ ≤ D * (C * ‖p - q‖) := mul_le_mul_of_nonneg_left ((hC i p hp).2 q hq) hD0
      _ ≤ (D + D * C) * ‖p - q‖ := by
          have := norm_nonneg (p - q)
          nlinarith [mul_nonneg hD0 this]

/-- The bound and Lipschitz constant as an explicit Lipschitz property. -/
theorem lipschitzOnWith {f : ι → P → ℂ} (hf : UniformLipOn f B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, (∀ p ∈ B, ‖f i p‖ ≤ C) ∧ LipschitzOnWith (Real.toNNReal C) (f i) B := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨C, hC0, fun i => ⟨fun p hp => (hC i p hp).1, LipschitzOnWith.of_dist_le' ?_⟩⟩
  intro p hp q hq
  rw [dist_eq_norm, dist_eq_norm]
  exact (hC i p hp).2 q hq

end UniformLipOn

/-! ### Uniform bounds from joint smoothness -/

/-- **A jointly `C¹` function on a neighbourhood of `K × B` is uniformly Lipschitz on `B`**, for
`K` compact and `B` compact convex. -/
theorem uniformLipOn_of_contDiffAt {X P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : X × P → ℂ} {K : Set X} (hK : IsCompact K)
    {B : Set P} (hB : IsCompact B) (hconv : Convex ℝ B)
    (smooth : ∀ k ∈ K, ∀ p ∈ B, ContDiffAt ℝ 1 f (k, p)) :
    UniformLipOn (fun (k : K) p => f (k.val, p)) B := by
  have compact : IsCompact (K ×ˢ B) := hK.prod hB
  have value : ContinuousOn f (K ×ˢ B) := fun x hx =>
    (smooth x.1 hx.1 x.2 hx.2).continuousAt.continuousWithinAt
  have derivative : ContinuousOn (fun x => ‖fderiv ℝ f x‖) (K ×ˢ B) := fun x hx =>
    ((smooth x.1 hx.1 x.2 hx.2).fderiv_right (m := 0) (by norm_num)).continuousAt.norm
      |>.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := compact.exists_bound_of_continuousOn value
  obtain ⟨C₂, hC₂⟩ := compact.exists_bound_of_continuousOn derivative
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun k p hp => ⟨?_, fun q hq => ?_⟩⟩
  · exact (hC₁ (k.val, p) ⟨k.property, hp⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have slice : ∀ x ∈ B, HasFDerivWithinAt (fun p => f (k.val, p))
        ((fderiv ℝ f (k.val, x)).comp (ContinuousLinearMap.inr ℝ X P)) B x := fun x hx =>
      ((smooth k.val k.property x hx).differentiableAt (by norm_num)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_right k.val x) |>.hasFDerivWithinAt
    have bound : ∀ x ∈ B, ‖(fderiv ℝ f (k.val, x)).comp (ContinuousLinearMap.inr ℝ X P)‖ ≤
        max (max C₁ C₂) 0 := by
      intro x hx
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have inr : ‖ContinuousLinearMap.inr ℝ X P‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp
      have := hC₂ (k.val, x) ⟨k.property, hx⟩
      rw [Real.norm_of_nonneg (norm_nonneg _)] at this
      calc ‖fderiv ℝ f (k.val, x)‖ * ‖ContinuousLinearMap.inr ℝ X P‖ ≤ C₂ * 1 :=
            mul_le_mul this inr (norm_nonneg _) ((norm_nonneg _).trans this)
        _ ≤ _ := by rw [mul_one]; exact (le_max_right _ _).trans (le_max_left _ _)
    exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le slice bound hq hp

/-! ### Differentiation under the integral -/

/-- **Differentiation under the integral** for integrands `T(u) · f u p` with `‖T‖` integrable and
`f` uniformly Lipschitz near `p₀`. -/
theorem hasFDerivAt_integral_of_uniformLipOn {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] {I : P → α → ℂ} {T : α → ℂ} {f : α → P → ℂ}
    {B : Set P} {p₀ : P} (hB : B ∈ 𝓝 p₀) (scale : Integrable (fun u => ‖T u‖) μ)
    (equal : ∀ p ∈ B, ∀ u, I p u = T u * f u p) (uniform : UniformLipOn f B)
    (measurable : ∀ p, AEStronglyMeasurable (I p) μ)
    (differentiable : ∀ u, DifferentiableAt ℝ (fun p => I p u) p₀) :
    HasFDerivAt (fun p => ∫ u, I p u ∂μ) (∫ u, fderiv ℝ (fun p => I p u) p₀ ∂μ) p₀ := by
  obtain ⟨C, hC0, hC⟩ := uniform
  have bound_integrable : Integrable (fun u => C * ‖T u‖) μ := scale.const_mul C
  have value_integrable : Integrable (I p₀) μ := by
    refine bound_integrable.mono' (measurable p₀) (Eventually.of_forall fun u => ?_)
    rw [equal p₀ (mem_of_mem_nhds hB), norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC u p₀ (mem_of_mem_nhds hB)).1 (norm_nonneg _)
  have lipschitz : ∀ᵐ u ∂μ, LipschitzOnWith (Real.nnabs (C * ‖T u‖)) (fun p => I p u) B := by
    refine Eventually.of_forall fun u => LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [dist_eq_norm, dist_eq_norm, equal p hp, equal q hq, ← mul_sub, norm_mul,
      Real.coe_nnabs, abs_of_nonneg (by positivity)]
    calc ‖T u‖ * ‖f u p - f u q‖ ≤ ‖T u‖ * (C * ‖p - q‖) :=
          mul_le_mul_of_nonneg_left ((hC u p hp).2 q hq) (norm_nonneg _)
      _ = C * ‖T u‖ * ‖p - q‖ := by ring
  have derivative : ∀ᵐ u ∂μ, HasFDerivAt (fun p => I p u) (fderiv ℝ (fun p => I p u) p₀) p₀ :=
    Eventually.of_forall fun u => (differentiable u).hasFDerivAt
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip hB (Eventually.of_forall measurable)
    value_integrable (aestronglyMeasurable_of_hasFDerivAt measurable derivative) lipschitz
    bound_integrable derivative).2

/-- **Differentiation under the integral** in one real variable. -/
theorem hasDerivAt_integral_of_uniformLipOn {I : ℝ → α → ℂ} {T : α → ℂ} {f : α → ℝ → ℂ}
    {B : Set ℝ} {p₀ : ℝ} (hB : B ∈ 𝓝 p₀) (scale : Integrable (fun u => ‖T u‖) μ)
    (equal : ∀ p ∈ B, ∀ u, I p u = T u * f u p) (uniform : UniformLipOn f B)
    (measurable : ∀ p, AEStronglyMeasurable (I p) μ)
    (differentiable : ∀ u, DifferentiableAt ℝ (fun p => I p u) p₀) :
    HasDerivAt (fun p => ∫ u, I p u ∂μ) (∫ u, deriv (fun p => I p u) p₀ ∂μ) p₀ := by
  obtain ⟨C, hC0, hC⟩ := uniform
  have bound_integrable : Integrable (fun u => C * ‖T u‖) μ := scale.const_mul C
  have value_integrable : Integrable (I p₀) μ := by
    refine bound_integrable.mono' (measurable p₀) (Eventually.of_forall fun u => ?_)
    rw [equal p₀ (mem_of_mem_nhds hB), norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC u p₀ (mem_of_mem_nhds hB)).1 (norm_nonneg _)
  have lipschitz : ∀ᵐ u ∂μ, LipschitzOnWith (Real.nnabs (C * ‖T u‖)) (fun p => I p u) B := by
    refine Eventually.of_forall fun u => LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [dist_eq_norm, dist_eq_norm, equal p hp, equal q hq, ← mul_sub, norm_mul,
      Real.coe_nnabs, abs_of_nonneg (by positivity)]
    calc ‖T u‖ * ‖f u p - f u q‖ ≤ ‖T u‖ * (C * ‖p - q‖) :=
          mul_le_mul_of_nonneg_left ((hC u p hp).2 q hq) (norm_nonneg _)
      _ = C * ‖T u‖ * ‖p - q‖ := by ring
  have derivative : ∀ᵐ u ∂μ, HasDerivAt (fun p => I p u) (deriv (fun p => I p u) p₀) p₀ :=
    Eventually.of_forall fun u => (differentiable u).hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_lip hB (Eventually.of_forall measurable)
    value_integrable (aestronglyMeasurable_of_hasDerivAt measurable derivative) lipschitz
    bound_integrable derivative).2

end TernaryPeriodPolynomials.AnalyticClasses
