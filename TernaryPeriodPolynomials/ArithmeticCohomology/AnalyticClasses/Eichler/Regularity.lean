module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.Normal

@[expose] public section


/-!
# Regularity of the pointwise Eichler period

For a family `F h` of holomorphic functions on the upper half plane, locally bounded uniformly in
`h`, each weight-basis coordinate of the straight-line Eichler period
`Per_F(z)(h) = ∫_i^z F h w (X₀ - w X₁)^{n+1} dw` is a holomorphic function of `z` whose complex
derivative is the kernel `F h z · coord_j ((X₀ - z X₁)^{n+1})`. The kernel and its derivative are
bounded on compact sets uniformly in `h` (Cauchy estimate), which gives a uniform second-order
Taylor bound on compact convex sets. The reflected period `z ↦ Per_F(-conj z)` is real
differentiable.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ}

/-- The monomial `X₀^m X₁^(d-m)` as a homogeneous binary form of degree `d`. -/
def pointMonomial (d : ℕ) (m : Fin (d + 1)) : Binary.HomogeneousPoly d :=
  ⟨X 0 ^ (m : ℕ) * X 1 ^ (d - m), by
    rw [mem_homogeneousSubmodule]
    have hm : (m : ℕ) + (d - m) = d := by omega
    simpa only [hm] using ((isHomogeneous_X_pow (R := ℂ) (0 : Fin 2) (m : ℕ)).mul
      (isHomogeneous_X_pow (R := ℂ) (1 : Fin 2) (d - m)))⟩

theorem binaryPointPower_eq_sum (d : ℕ) (w : ℂ) :
    binaryPointPower d w =
      ∑ m : Fin (d + 1), ((-w) ^ (d - m) * (d.choose m : ℂ)) • pointMonomial d m := by
  apply Subtype.ext
  simp only [binaryPointPower, Submodule.coe_sum, Submodule.coe_smul, pointMonomial]
  rw [sub_eq_add_neg, add_pow, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.smul_eq_C_mul]
  have : -(C w * X 1 : Binary.Poly) = C (-w) * X 1 := by rw [map_neg, neg_mul]
  rw [this]
  simp only [mul_pow, map_mul, map_pow, map_natCast]
  ring

theorem coord_binaryPointPower (d : ℕ) (j : Fin (d + 1)) (w : ℂ) :
    (binaryWeightBasis d).coord j (binaryPointPower d w) =
      ∑ m : Fin (d + 1), (-w) ^ (d - m) * (d.choose m : ℂ) *
        (binaryWeightBasis d).coord j (pointMonomial d m) := by
  rw [binaryPointPower_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem differentiable_coord_binaryPointPower (d : ℕ) (j : Fin (d + 1)) :
    Differentiable ℂ (fun w => (binaryWeightBasis d).coord j (binaryPointPower d w)) := by
  simp only [coord_binaryPointPower]
  fun_prop

/-- The scalar Eichler kernel `F h w · coord_j ((X₀ - w X₁)^{n+1})`. -/
def eichlerKernel (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) (w : ℂ) : ℂ :=
  F h w * (binaryWeightBasis (n + 1)).coord j (binaryPointPower (n + 1) w)

theorem coord_eichlerPeriod (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F z h) =
      ∫ t in (0 : ℝ)..1, eichlerIntegrand n F z h j t := by
  rw [eichlerPeriod, Module.Basis.coord_apply, Module.Basis.repr_sum_self]

theorem eichlerIntegrand_eq (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) (t : ℝ) :
    eichlerIntegrand n F z h j t = (z - Complex.I) * eichlerKernel n F h j (eichlerPath z t) := by
  rw [eichlerIntegrand, eichlerKernel, mul_assoc]

theorem exists_ball_upperHalfPlane {z : ℂ} (hz : 0 < z.im) :
    ∃ c : ℂ, ∃ r : ℝ, Complex.I ∈ Metric.ball c r ∧ z ∈ Metric.ball c r ∧
      Metric.ball c r ⊆ {w : ℂ | 0 < w.im} := by
  set M : ℝ := ‖z‖ ^ 2 / (2 * z.im) + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨(M : ℂ) * Complex.I, M, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hMpos.le, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.I_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.mul_im]
    have : 0 < ‖z‖ ^ 2 / (2 * z.im) := by
      have : 0 < ‖z‖ := by
        rw [norm_pos_iff]; rintro rfl; simp at hz
      positivity
    nlinarith
  · rw [Metric.mem_ball, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hMpos.le, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, Complex.sub_im, Complex.mul_im]
    have key : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have h2 : ‖z‖ ^ 2 / (2 * z.im) * (2 * z.im) = ‖z‖ ^ 2 := by field_simp
    nlinarith
  · intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have him := (Complex.abs_im_le_norm (w - (M : ℂ) * Complex.I)).trans_lt hw
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re] at him
    rw [Set.mem_ofPred_eq]
    have := (abs_lt.mp him).1
    linarith

theorem eichlerPath_mem {s : Set ℂ} (hs : Convex ℝ s) (hI : Complex.I ∈ s) {w : ℂ}
    (hw : w ∈ s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : eichlerPath w t ∈ s :=
  hs.add_smul_sub_mem hI hw ht

theorem integral_eichlerPath_eq_sub {g G : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    (hI : Complex.I ∈ s) {w : ℂ} (hw : w ∈ s) (hg : ContinuousOn g s)
    (hG : ∀ ζ ∈ s, HasDerivAt G (g ζ) ζ) :
    ∫ t in (0 : ℝ)..1, (w - Complex.I) * g (eichlerPath w t) = G w - G Complex.I := by
  have hpath : ∀ t : ℝ, HasDerivAt (eichlerPath w) (w - Complex.I) t := by
    intro t
    have e : eichlerPath w = fun t : ℝ => Complex.I + (t : ℂ) * (w - Complex.I) := by
      funext t; simp [eichlerPath, Complex.real_smul]
    rw [e]
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (w - Complex.I)).const_add Complex.I
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, eichlerPath w t ∈ s := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact eichlerPath_mem hs hI hw ht
  have hcont : Continuous (eichlerPath w) := by
    unfold eichlerPath; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => G (eichlerPath w t))]
  · simp [eichlerPath]
  · intro t ht
    rw [mul_comm]
    exact (hG _ (hmem t ht)).comp t (hpath t)
  · apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (hg.comp hcont.continuousOn hmem)

theorem differentiableOn_eichlerKernel (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) : DifferentiableOn ℂ (eichlerKernel n F h j) {z : ℂ | 0 < z.im} :=
  (holomorphic h).mul (differentiable_coord_binaryPointPower (n + 1) j).differentiableOn

/-- **Holomorphy of the Eichler period.** -/
theorem hasDerivAt_coord_eichlerPeriod (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    HasDerivAt (fun w => (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h))
      (F h z * (binaryWeightBasis (n + 1)).coord j (binaryPointPower (n + 1) z)) z := by
  obtain ⟨c, r, hI, hzB, hB⟩ := exists_ball_upperHalfPlane hz
  have hdiff : DifferentiableOn ℂ (eichlerKernel n F h j) (Metric.ball c r) :=
    (differentiableOn_eichlerKernel F holomorphic h j).mono hB
  obtain ⟨G, hG⟩ := hdiff.isExactOn_ball
  have heq : ∀ w ∈ Metric.ball c r,
      (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h) = G w - G Complex.I := by
    intro w hw
    rw [coord_eichlerPeriod]
    simp only [eichlerIntegrand_eq]
    exact integral_eichlerPath_eq_sub (convex_ball c r) hI hw hdiff.continuousOn hG
  have hev : (fun w => (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h)) =ᶠ[nhds z]
      fun w => G w - G Complex.I :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hzB) heq
  exact ((hG z hzB).sub_const _).congr_of_eventuallyEq hev

theorem eichlerUpperSet_isOpen : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

/-- **Uniform bounds for the Eichler kernel and its derivative on compact sets.** -/
theorem exists_bound_eichlerKernel (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (bounded : ∀ K ⊆ {z : ℂ | 0 < z.im}, IsCompact K → ∃ C, ∀ h, ∀ w ∈ K, ‖F h w‖ ≤ C)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) (hKc : IsCompact K) (j : Fin (n + 2)) :
    ∃ C, ∀ h, ∀ w ∈ K, ‖eichlerKernel n F h j w‖ ≤ C ∧
      ‖deriv (eichlerKernel n F h j) w‖ ≤ C := by
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open eichlerUpperSet_isOpen hK
  have hLc : IsCompact (Metric.cthickening δ K) := hKc.cthickening
  obtain ⟨CF, hCF⟩ := bounded _ hsub hLc
  obtain ⟨CP, hCP⟩ := hLc.exists_bound_of_continuousOn
    (differentiable_coord_binaryPointPower (n + 1) j).continuous.continuousOn
  set B : ℝ := max CF 0 * max CP 0 with hB
  have hbound : ∀ h, ∀ w ∈ Metric.cthickening δ K, ‖eichlerKernel n F h j w‖ ≤ B := by
    intro h w hw
    rw [eichlerKernel, norm_mul]
    exact mul_le_mul ((hCF h w hw).trans (le_max_left _ _)) ((hCP w hw).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  refine ⟨max B (B / δ), fun h w hw => ⟨(hbound h w ?_).trans (le_max_left _ _), ?_⟩⟩
  · exact Metric.self_subset_cthickening K hw
  · have hball : Metric.closedBall w δ ⊆ Metric.cthickening δ K :=
      Metric.closedBall_subset_cthickening hw δ
    have hd : DiffContOnCl ℂ (eichlerKernel n F h j) (Metric.ball w δ) :=
      ((differentiableOn_eichlerKernel F holomorphic h j).mono hsub).diffContOnCl_ball hball
    refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hd fun ζ hζ => ?_).trans
      (le_max_right _ _)
    exact hbound h ζ (hball (Metric.sphere_subset_closedBall hζ))

/-- The bounds of `exists_bound_eichlerKernel`, with the kernel written out. -/
theorem exists_bound_eichlerKernel_explicit (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (bounded : ∀ K ⊆ {z : ℂ | 0 < z.im}, IsCompact K → ∃ C, ∀ h, ∀ w ∈ K, ‖F h w‖ ≤ C)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) (hKc : IsCompact K) (j : Fin (n + 2)) :
    ∃ C, ∀ h, ∀ w ∈ K,
      ‖F h w * (binaryWeightBasis (n + 1)).coord j (binaryPointPower (n + 1) w)‖ ≤ C ∧
      ‖deriv (fun v => F h v * (binaryWeightBasis (n + 1)).coord j
        (binaryPointPower (n + 1) v)) w‖ ≤ C :=
  exists_bound_eichlerKernel F holomorphic bounded hK hKc j

/-- **Second-order Taylor bound for the Eichler period** on a compact convex set. -/
theorem eichlerPeriod_taylor_bound (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (bounded : ∀ K ⊆ {z : ℂ | 0 < z.im}, IsCompact K → ∃ C, ∀ h, ∀ w ∈ K, ‖F h w‖ ≤ C)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (j : Fin (n + 2)) :
    ∃ C, ∀ h, ∀ z ∈ K, ∀ w ∈ K,
      ‖(binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h) -
          (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F z h) -
          eichlerKernel n F h j z * (w - z)‖ ≤ C * ‖w - z‖ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_bound_eichlerKernel F holomorphic bounded hK hKc j
  refine ⟨C, fun h z hz w hw => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC h z hz).1
  set g := eichlerKernel n F h j with hg
  have hgdiff : ∀ ζ ∈ K, DifferentiableAt ℂ g ζ := fun ζ hζ =>
    (differentiableOn_eichlerKernel F holomorphic h j).differentiableAt
      (eichlerUpperSet_isOpen.mem_nhds (hK hζ))
  have hlip : ∀ ζ ∈ K, ‖g ζ - g z‖ ≤ C * ‖ζ - z‖ := fun ζ hζ =>
    hKconv.norm_image_sub_le_of_norm_deriv_le hgdiff (fun x hx => (hC h x hx).2) hz hζ
  have hseg : segment ℝ z w ⊆ K := hKconv.segment_subset hz hw
  have hderiv : ∀ ζ ∈ segment ℝ z w,
      HasDerivWithinAt (fun ζ => (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F ζ h) -
        g z * ζ) (g ζ - g z) (segment ℝ z w) ζ := by
    intro ζ hζ
    have h1 := hasDerivAt_coord_eichlerPeriod F holomorphic (hK (hseg hζ)) h j
    have h2 : HasDerivAt (fun y => g z * y) (g z) ζ := by
      simpa using (hasDerivAt_id ζ).const_mul (g z)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ ζ ∈ segment ℝ z w, ‖g ζ - g z‖ ≤ C * ‖w - z‖ := fun ζ hζ =>
    (hlip ζ (hseg hζ)).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hζ) hC0)
  have := (convex_segment z w).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  calc _ = ‖(binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h) - g z * w -
        ((binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F z h) - g z * z)‖ := by
        congr 1; ring
    _ ≤ C * ‖w - z‖ * ‖w - z‖ := this
    _ = C * ‖w - z‖ ^ 2 := by ring

theorem binaryComplexReflection_mem {z : ℂ} (hz : 0 < z.im) :
    0 < (binaryComplexReflection z).im := by
  rwa [binaryComplexReflection_im]

theorem norm_binaryComplexReflection (z : ℂ) : ‖binaryComplexReflection z‖ = ‖z‖ := by
  simp [binaryComplexReflection]

/-- **Real differentiability of the reflected Eichler period.** -/
theorem hasFDerivAt_coord_eichlerPeriod_reflection (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    HasFDerivAt (fun w => (binaryWeightBasis (n + 1)).coord j
        (eichlerPeriod n F (binaryComplexReflection w) h))
      ((F h (binaryComplexReflection z) * (binaryWeightBasis (n + 1)).coord j
        (binaryPointPower (n + 1) (binaryComplexReflection z))) • binaryComplexReflection) z := by
  have h1 := ((hasDerivAt_coord_eichlerPeriod F holomorphic (binaryComplexReflection_mem hz) h
    j).hasFDerivAt.restrictScalars ℝ).comp z binaryComplexReflection.hasFDerivAt
  refine h1.congr_fderiv (ContinuousLinearMap.ext fun dw => ?_)
  simp [mul_comm]

end TernaryPeriodPolynomials.AnalyticClasses
