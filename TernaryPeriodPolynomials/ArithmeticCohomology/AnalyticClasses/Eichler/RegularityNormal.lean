module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.Regularity

@[expose] public section


/-!
# Real differentiability of the pointwise Eichler normal form

The pointwise normal form `½ (Per_F(w)(h) + J · Per_F(-conj w)(h))`, viewed as a function of the
point `w` of the upper half plane, has real-differentiable weight-basis coordinates with an
explicit derivative. The derivative is bounded on compact sets uniformly in `h`, and on compact
convex sets the coordinates satisfy a second-order Taylor bound uniform in `h`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ}

/-- The pointwise Eichler normal form as a function of the point `w` of the upper half plane:
`½ (Per_F(w)(h) + J · Per_F(-conj w)(h))`. -/
def eichlerPointNormal (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (w : ℂ) (h : BinaryAdelicGL) :
    Binary.HomogeneousPoly (n + 1) :=
  (2 : ℂ)⁻¹ • (eichlerPeriod n F w h + binaryAmbientRepresentation n UpperHalfPlane.J
    (eichlerPeriod n F (binaryComplexReflection w)) h)

theorem eichlerNormal_eq_eichlerPointNormal (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) : eichlerNormal n F A h = eichlerPointNormal n F (basePoint A) h := rfl

/-- The matrix coefficient of the cohomological action of `J` in the weight basis. -/
def eichlerReflectionCoeff (n : ℕ) (j i : Fin (n + 2)) : ℂ :=
  normPower (GeneralLinearGroup.det (atInfinity UpperHalfPlane.J)) (((n : ℂ) + 3) / 2) *
    (binaryWeightBasis (n + 1)).coord j
      (binaryCoefficient n UpperHalfPlane.J (binaryWeightBasis (n + 1) i))

theorem coord_eichlerPointNormal (F : BinaryAdelicGL → ℂ → ℂ) (w : ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h) =
      (2 : ℂ)⁻¹ * ((binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h) +
        ∑ i, eichlerReflectionCoeff n j i * (binaryWeightBasis (n + 1)).coord i
          (eichlerPeriod n F (binaryComplexReflection w) (h * atInfinity UpperHalfPlane.J))) := by
  have hrep : binaryAmbientRepresentation n UpperHalfPlane.J
      (eichlerPeriod n F (binaryComplexReflection w)) h =
      binaryCohomologicalAction n UpperHalfPlane.J
        (eichlerPeriod n F (binaryComplexReflection w)) h := rfl
  rw [eichlerPointNormal, hrep, binaryCohomologicalAction]
  conv_lhs => rw [← (binaryWeightBasis (n + 1)).sum_repr
    (eichlerPeriod n F (binaryComplexReflection w) (h * atInfinity UpperHalfPlane.J))]
  simp only [map_smul, map_add, map_sum, smul_eq_mul, eichlerReflectionCoeff,
    Module.Basis.coord_apply, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The real derivative at `z` of the `j`-th coordinate of the pointwise Eichler normal form. -/
def eichlerPointNormalDeriv (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) : ℂ →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • (eichlerKernel n F h j z • ContinuousLinearMap.id ℝ ℂ +
    ∑ i, (eichlerReflectionCoeff n j i * eichlerKernel n F (h * atInfinity UpperHalfPlane.J) i
      (binaryComplexReflection z)) • binaryComplexReflection)

theorem eichlerPointNormalDeriv_apply (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) (dw : ℂ) :
    eichlerPointNormalDeriv n F z h j dw =
      (2 : ℂ)⁻¹ * (eichlerKernel n F h j z * dw +
        ∑ i, eichlerReflectionCoeff n j i * eichlerKernel n F (h * atInfinity UpperHalfPlane.J) i
          (binaryComplexReflection z) * binaryComplexReflection dw) := by
  simp [eichlerPointNormalDeriv, mul_add]

/-- **Real differentiability of the pointwise Eichler normal form.** -/
theorem hasFDerivAt_coord_eichlerPointNormal (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    HasFDerivAt (fun w => (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h))
      (eichlerPointNormalDeriv n F z h j) z := by
  have e : (fun w => (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h)) =
      fun w => (2 : ℂ)⁻¹ * ((binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h) +
        ∑ i, eichlerReflectionCoeff n j i * (binaryWeightBasis (n + 1)).coord i
          (eichlerPeriod n F (binaryComplexReflection w) (h * atInfinity UpperHalfPlane.J))) :=
    funext fun w => coord_eichlerPointNormal F w h j
  rw [e]
  have h1 := (hasDerivAt_coord_eichlerPeriod F holomorphic hz h j).hasFDerivAt.restrictScalars ℝ
  have h2 := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasFDerivAt_coord_eichlerPeriod_reflection F holomorphic hz
      (h * atInfinity UpperHalfPlane.J) i).const_mul (eichlerReflectionCoeff n j i)
  refine ((h1.add h2).const_mul (2 : ℂ)⁻¹).congr_fderiv (ContinuousLinearMap.ext fun dw => ?_)
  rw [eichlerPointNormalDeriv_apply]
  simp only [_root_.smul_apply, _root_.add_apply,
    FunLike.coe_sum, Finset.sum_apply, smul_eq_mul,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    eichlerKernel]
  congr 2
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

theorem reflection_image_subset {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) :
    binaryComplexReflection '' K ⊆ {z : ℂ | 0 < z.im} := by
  rintro _ ⟨w, hw, rfl⟩
  exact binaryComplexReflection_mem (hK hw)

theorem norm_binaryComplexReflection_le : ‖binaryComplexReflection‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [norm_binaryComplexReflection, one_mul]

/-- **Uniform bound for the derivative of the pointwise Eichler normal form** on compact sets. -/
theorem exists_bound_eichlerPointNormalDeriv (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (bounded : ∀ K ⊆ {z : ℂ | 0 < z.im}, IsCompact K → ∃ C, ∀ h, ∀ w ∈ K, ‖F h w‖ ≤ C)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) (hKc : IsCompact K) (j : Fin (n + 2)) :
    ∃ C, ∀ h, ∀ w ∈ K, ‖eichlerPointNormalDeriv n F w h j‖ ≤ C := by
  obtain ⟨C0, hC0⟩ := exists_bound_eichlerKernel F holomorphic bounded hK hKc j
  have hr := fun i : Fin (n + 2) => exists_bound_eichlerKernel F holomorphic bounded
    (reflection_image_subset hK) (hKc.image binaryComplexReflection.continuous) i
  choose Cr hCr using hr
  refine ⟨‖(2 : ℂ)⁻¹‖ * (max C0 0 + ∑ i, ‖eichlerReflectionCoeff n j i‖ * max (Cr i) 0),
    fun h w hw => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    have := fun i : Fin (n + 2) => le_max_right (Cr i) 0
    positivity) fun dw => ?_
  rw [eichlerPointNormalDeriv_apply, norm_mul, mul_assoc]
  gcongr
  calc _ ≤ ‖eichlerKernel n F h j w * dw‖ + ∑ i, ‖eichlerReflectionCoeff n j i *
        eichlerKernel n F (h * atInfinity UpperHalfPlane.J) i (binaryComplexReflection w) *
          binaryComplexReflection dw‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ max C0 0 * ‖dw‖ + ∑ i, ‖eichlerReflectionCoeff n j i‖ * max (Cr i) 0 * ‖dw‖ := by
        refine add_le_add ?_ (Finset.sum_le_sum fun i _ => ?_)
        · rw [norm_mul]
          gcongr
          exact (hC0 h w hw).1.trans (le_max_left _ _)
        · rw [norm_mul, norm_mul, norm_binaryComplexReflection]
          gcongr
          exact (hCr i _ _ (Set.mem_image_of_mem _ hw)).1.trans (le_max_left _ _)
    _ = _ := by rw [add_mul, Finset.sum_mul]

/-- **Second-order Taylor bound for the pointwise Eichler normal form**, uniform in `h`, on a
compact convex subset of the upper half plane. -/
theorem eichlerPointNormal_taylor_bound (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (bounded : ∀ K ⊆ {z : ℂ | 0 < z.im}, IsCompact K → ∃ C, ∀ h, ∀ w ∈ K, ‖F h w‖ ≤ C)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (j : Fin (n + 2)) :
    ∃ C, ∀ h, ∀ z ∈ K, ∀ w ∈ K,
      ‖(binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h) -
          (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F z h) -
          eichlerPointNormalDeriv n F z h j (w - z)‖ ≤ C * ‖w - z‖ ^ 2 := by
  obtain ⟨C0, hC0⟩ := eichlerPeriod_taylor_bound F holomorphic bounded hK hKc hKconv j
  have hconv : Convex ℝ (binaryComplexReflection '' K) := by
    simpa using hKconv.linear_image binaryComplexReflection.toLinearMap
  have hr := fun i : Fin (n + 2) => eichlerPeriod_taylor_bound F holomorphic bounded
    (reflection_image_subset hK) (hKc.image binaryComplexReflection.continuous) hconv i
  choose Cr hCr using hr
  refine ⟨‖(2 : ℂ)⁻¹‖ * (max C0 0 + ∑ i, ‖eichlerReflectionCoeff n j i‖ * max (Cr i) 0),
    fun h z hz w hw => ?_⟩
  set h' := h * atInfinity UpperHalfPlane.J
  set rz := binaryComplexReflection z
  set rw' := binaryComplexReflection w
  have hrsub : binaryComplexReflection (w - z) = rw' - rz := map_sub _ _ _
  have hnorm : ‖rw' - rz‖ = ‖w - z‖ := by rw [← hrsub, norm_binaryComplexReflection]
  set T0 := (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h) -
    (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F z h) -
    eichlerKernel n F h j z * (w - z) with hT0
  set T : Fin (n + 2) → ℂ := fun i => (binaryWeightBasis (n + 1)).coord i
    (eichlerPeriod n F rw' h') - (binaryWeightBasis (n + 1)).coord i (eichlerPeriod n F rz h') -
    eichlerKernel n F h' i rz * (rw' - rz) with hT
  have hid : (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h) -
      (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F z h) -
      eichlerPointNormalDeriv n F z h j (w - z) =
      (2 : ℂ)⁻¹ * (T0 + ∑ i, eichlerReflectionCoeff n j i * T i) := by
    rw [coord_eichlerPointNormal, coord_eichlerPointNormal, eichlerPointNormalDeriv_apply, hrsub]
    simp only [hT0, hT, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  have hT0b : ‖T0‖ ≤ max C0 0 * ‖w - z‖ ^ 2 :=
    (hC0 h z hz w hw).trans (by gcongr; exact le_max_left _ _)
  have hTb : ∀ i, ‖eichlerReflectionCoeff n j i * T i‖ ≤
      ‖eichlerReflectionCoeff n j i‖ * max (Cr i) 0 * ‖w - z‖ ^ 2 := by
    intro i
    rw [norm_mul, mul_assoc]
    gcongr
    calc ‖T i‖ ≤ Cr i * ‖rw' - rz‖ ^ 2 :=
          hCr i h' rz (Set.mem_image_of_mem _ hz) rw' (Set.mem_image_of_mem _ hw)
      _ ≤ max (Cr i) 0 * ‖w - z‖ ^ 2 := by rw [hnorm]; gcongr; exact le_max_left _ _
  rw [hid, norm_mul, mul_assoc]
  gcongr
  calc ‖T0 + ∑ i, eichlerReflectionCoeff n j i * T i‖
      ≤ ‖T0‖ + ∑ i, ‖eichlerReflectionCoeff n j i * T i‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ max C0 0 * ‖w - z‖ ^ 2 +
        ∑ i, ‖eichlerReflectionCoeff n j i‖ * max (Cr i) 0 * ‖w - z‖ ^ 2 :=
        add_le_add hT0b (Finset.sum_le_sum fun i _ => hTb i)
    _ = _ := by rw [← Finset.sum_mul]; ring

end TernaryPeriodPolynomials.AnalyticClasses
