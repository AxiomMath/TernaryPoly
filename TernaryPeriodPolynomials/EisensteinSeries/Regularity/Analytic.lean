module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Equivariance
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Sobolev

@[expose] public section


/-!
# Analyticity of realized smooth vectors

The realization is not continuous on the Hilbert space, but at a fixed point `y` and level `U`
it is bounded by the norm of the second rotation derivative (`norm_realizeRegAt_le`, from the
Sobolev-type bound). By Hahn–Banach and the Riesz representation theorem it is therefore of the
form `F ↦ ⟪b, secondRot F⟫` (`exists_inner_secondRot`). For a smooth vector `F` the map
`A ↦ secondRot (realRep (invertibleMatrix A) F)` is real analytic on the invertible matrices: it
is `Y''(A)(XA, XA) + Y'(A)(X²A)` for the analytic orbit map `Y` and the rotation generator `X`
(`secondRot_orbitMap`). Composing with `⟪b, ·⟫` gives the analyticity of
`x ↦ realizeFun F (g · x)` along `GL₂(ℝ)` (`realizeFun_scalarSmooth`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise InnerProductSpace
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Regularity

noncomputable instance bergmanDerivativeSpace {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] BergmanSpace k E) :=
  ContinuousLinearMap.toNormedSpace

variable {k : ℕ} (M : FiniteModel k)

/-! ### Representing the realization at a point -/

section Representing

variable (U : Subgroup BinaryFiniteGL)

/-- Vectors with `U`-fixed values and smooth rotation orbits. -/
def regularSubmodule : Submodule ℂ (BergmanSpace k M.E) where
  carrier := {F | (∀ w, F w ∈ fixedSubmodule M.σ U) ∧ IsRotSmooth F}
  add_mem' hF hG := ⟨fun w => Submodule.add_mem _ (hF.1 w) (hG.1 w), hF.2.add hG.2⟩
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, isRotSmooth_zero⟩
  smul_mem' c _ hF := ⟨fun w => Submodule.smul_mem _ c (hF.1 w), hF.2.smul c⟩

/-- The second rotation derivative on the regular vectors. -/
def secondRotReg : regularSubmodule M U →ₗ[ℂ] BergmanSpace k M.E where
  toFun F := secondRot (F : BergmanSpace k M.E)
  map_add' F G := secondRot_add F.2.2 G.2.2
  map_smul' c F := secondRot_smul c F.2.2

variable {U} (hU : IsOpenCompact U)

/-- The realization at the point `y`, on the regular vectors. -/
def realizeRegAt (hk : 6 ≤ k) (y : BinaryAdelicGL) : regularSubmodule M U →ₗ[ℂ] ℂ where
  toFun F := realizeU M hU (F : BergmanSpace k M.E) y
  map_add' F G := congrFun (realizeU_add M hU (L1Finite.of_isRotSmooth hk F.2.2)
    (L1Finite.of_isRotSmooth hk G.2.2)) y
  map_smul' c F := congrFun (realizeU_smul M hU c (F : BergmanSpace k M.E)) y

/-- The realization at a point is bounded by the second rotation derivative. -/
theorem norm_realizeRegAt_le (hk : 6 ≤ k) (y : BinaryAdelicGL) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : regularSubmodule M U,
      ‖realizeRegAt M hU hk y F‖ ≤ K * ‖secondRot (F : BergmanSpace k M.E)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_evalU M hU
  refine ⟨C * sobolevConst k, mul_nonneg hC0 (sobolevConst_nonneg k), fun F => ?_⟩
  have h1 := norm_realizeU_le M hU hC (L1Finite.of_isRotSmooth hk F.2.2) y
  have h2 := l1Integral_le_secondRot hk F.2.2
  have h3 : ∫ w, ‖(F : BergmanSpace k M.E) w‖ * |w.im| ^ ((k : ℝ) / 2) ∂hypMeasure =
      (l1Integral (F : BergmanSpace k M.E)).toReal := by
    rw [l1Integral, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun w => mul_nonneg (norm_nonneg _) (by positivity))
      (aestronglyMeasurable_l1 _)]
  have h4 : (l1Integral (F : BergmanSpace k M.E)).toReal ≤
      sobolevConst k * ‖secondRot (F : BergmanSpace k M.E)‖ :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (sobolevConst_nonneg k) (norm_nonneg _)) h2
  calc ‖realizeRegAt M hU hk y F‖ = ‖realizeU M hU (F : BergmanSpace k M.E) y‖ := rfl
    _ ≤ C * ∫ w, ‖(F : BergmanSpace k M.E) w‖ * |w.im| ^ ((k : ℝ) / 2) ∂hypMeasure := h1
    _ = C * (l1Integral (F : BergmanSpace k M.E)).toReal := by rw [h3]
    _ ≤ C * (sobolevConst k * ‖secondRot (F : BergmanSpace k M.E)‖) :=
        mul_le_mul_of_nonneg_left h4 hC0
    _ = C * sobolevConst k * ‖secondRot (F : BergmanSpace k M.E)‖ := by ring

/-- **The b-trick.** At a fixed point and level the realization is `F ↦ ⟪b, secondRot F⟫`. -/
theorem exists_inner_secondRot (hk : 6 ≤ k) (y : BinaryAdelicGL) :
    ∃ b : BergmanSpace k M.E, ∀ F : BergmanSpace k M.E,
      (∀ w, F w ∈ fixedSubmodule M.σ U) → IsRotSmooth F →
        realizeU M hU F y = ⟪b, secondRot F⟫_ℂ := by
  have : Fact (2 ≤ k) := ⟨by omega⟩
  obtain ⟨K, -, hK⟩ := norm_realizeRegAt_le M hU hk y
  have hker : LinearMap.ker (secondRotReg M U) ≤ LinearMap.ker (realizeRegAt M hU hk y) := by
    intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h := hK F
    have hF' : secondRot (F : BergmanSpace k M.E) = 0 := hF
    rw [hF', norm_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h
  let φ₀ : LinearMap.range (secondRotReg M U) →ₗ[ℂ] ℂ :=
    (LinearMap.ker (secondRotReg M U)).liftQ (realizeRegAt M hU hk y) hker ∘ₗ
      (LinearMap.quotKerEquivRange (secondRotReg M U)).symm.toLinearMap
  have hφ₀ : ∀ F : regularSubmodule M U,
      φ₀ ⟨secondRotReg M U F, LinearMap.mem_range_self _ F⟩ = realizeRegAt M hU hk y F := by
    intro F
    simp only [φ₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hbound : ∀ v : LinearMap.range (secondRotReg M U), ‖φ₀ v‖ ≤ K * ‖v‖ := by
    rintro ⟨v, F, rfl⟩
    rw [hφ₀]
    exact hK F
  let φc : StrongDual ℂ (LinearMap.range (secondRotReg M U)) := φ₀.mkContinuous K hbound
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range (secondRotReg M U)) φc
  refine ⟨(InnerProductSpace.toDual ℂ (BergmanSpace k M.E)).symm g, fun F hFU hFs => ?_⟩
  let F' : regularSubmodule M U := ⟨F, hFU, hFs⟩
  calc realizeU M hU F y = realizeRegAt M hU hk y F' := rfl
    _ = φ₀ ⟨secondRotReg M U F', LinearMap.mem_range_self _ F'⟩ := (hφ₀ F').symm
    _ = φc ⟨secondRotReg M U F', LinearMap.mem_range_self _ F'⟩ := rfl
    _ = g (secondRotReg M U F') := (hg _).symm
    _ = ⟪(InnerProductSpace.toDual ℂ (BergmanSpace k M.E)).symm g, secondRot F⟫_ℂ :=
        InnerProductSpace.toDual_symm_apply.symm

end Representing

/-! ### The orbit map and its second rotation derivative -/

/-- The generator `!![0, -1; 1, 0]` of the rotations. -/
def rotGen : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem rotGL_val_eq (θ : ℝ) :
    (rotGL θ).val = Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin θ • rotGen := by
  rw [rotGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotGen]

theorem rotGen_mul_rotGL_val (θ : ℝ) :
    rotGen * (rotGL θ).val = -Real.sin θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Real.cos θ • rotGen := by
  rw [rotGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotGen, Matrix.mul_apply, Fin.sum_univ_two]

theorem hasDerivAt_rotGL_val (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (rotGL t).val) (rotGen * (rotGL θ).val) θ := by
  have h := ((Real.hasDerivAt_cos θ).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)).add
    ((Real.hasDerivAt_sin θ).smul_const rotGen)
  rw [rotGen_mul_rotGL_val]
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall rotGL_val_eq)

/-- Left multiplication by a matrix, as a continuous linear map. -/
def mulLeftL (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

/-- Right multiplication by a matrix, as a continuous linear map. -/
def mulRightL (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ A)

theorem mulLeftL_apply (X A : Matrix (Fin 2) (Fin 2) ℝ) : mulLeftL X A = X * A := rfl

theorem mulRightL_apply (A B : Matrix (Fin 2) (Fin 2) ℝ) : mulRightL A B = B * A := rfl

/-- The invertible real matrices. -/
def detNeZero : Set (Matrix (Fin 2) (Fin 2) ℝ) := {A | A.det ≠ 0}

theorem isOpen_detNeZero : IsOpen detNeZero :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem invertibleMatrix_mul (g : GL (Fin 2) ℝ) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.det ≠ 0) : invertibleMatrix (g.val * A) = g * invertibleMatrix A := by
  have hgA : (g.val * A).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (gl_det_ne_zero g) hA
  apply Units.ext
  rw [Units.val_mul]
  unfold invertibleMatrix
  rw [dite_eq_left hgA, dite_eq_left hA, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

variable {M}

/-- The orbit map `A ↦ realRep (invertibleMatrix A) F`. -/
def orbitMap (F : BergmanSpace k M.E) (A : Matrix (Fin 2) (Fin 2) ℝ) : BergmanSpace k M.E :=
  realRep k M.E (invertibleMatrix A) F

theorem realRep_rot_orbitMap (F : BergmanSpace k M.E) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ detNeZero) (θ : ℝ) :
    realRep k M.E (rotGL θ) (orbitMap F A) = orbitMap F ((rotGL θ).val * A) := by
  rw [orbitMap, orbitMap, invertibleMatrix_mul _ hA, map_mul, Module.End.mul_apply]

/-- The orbit map of a smooth vector is real analytic on the invertible matrices. -/
theorem contDiffOn_orbitMap (F : smoothSubmodule (bergmanRep M)) :
    ContDiffOn ℝ ⊤ (orbitMap F.val) detNeZero := by
  have hs := (mem_smoothSubmodule.mp F.property).1
  have hι : ContDiff ℝ ⊤ fun A : Matrix (Fin 2) (Fin 2) ℝ => (fun _ : Fin 1 => A) :=
    contDiff_pi.mpr fun _ => contDiff_id
  have h := hs.comp hι.contDiffOn fun A hA _ => hA
  refine h.congr fun A _ => ?_
  simp only [Function.comp, orbitMap, bergmanRep_atInfinity]

/-- The explicit second rotation derivative of the orbit map. -/
def secondRotExpr (F : BergmanSpace k M.E) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    BergmanSpace k M.E :=
  fderiv ℝ (fderiv ℝ (orbitMap F)) A (rotGen * A) (rotGen * A) +
    fderiv ℝ (orbitMap F) A (rotGen * (rotGen * A))

theorem secondRot_orbitMap (F : smoothSubmodule (bergmanRep M))
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ∈ detNeZero) :
    secondRot (orbitMap F.val A) = secondRotExpr F.val A := by
  have hY := contDiffOn_orbitMap F
  have hY' : ContDiffOn ℝ ⊤ (fderiv ℝ (orbitMap F.val)) detNeZero :=
    hY.fderiv_of_isOpen isOpen_detNeZero (by simp)
  have hdiff : ∀ B ∈ detNeZero, DifferentiableAt ℝ (orbitMap F.val) B := fun B hB =>
    (hY.differentiableOn (by simp) B hB).differentiableAt (isOpen_detNeZero.mem_nhds hB)
  have hdiff' : ∀ B ∈ detNeZero, DifferentiableAt ℝ (fderiv ℝ (orbitMap F.val)) B :=
    fun B hB =>
      (hY'.differentiableOn (by simp) B hB).differentiableAt (isOpen_detNeZero.mem_nhds hB)
  have hRA : ∀ θ : ℝ, (rotGL θ).val * A ∈ detNeZero := fun θ => by
    change ((rotGL θ).val * A).det ≠ 0
    rw [Matrix.det_mul, det_rotGL, one_mul]
    exact hA
  have hcurve : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => (rotGL t).val * A)
      (rotGen * ((rotGL θ).val * A)) θ := fun θ => by
    have h : HasDerivAt (fun t : ℝ => (rotGL t).val * A)
        (mulRightL A (rotGen * (rotGL θ).val)) θ :=
      (mulRightL A).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_rotGL_val θ)
    have e : mulRightL A (rotGen * (rotGL θ).val) = rotGen * ((rotGL θ).val * A) := by
      rw [mulRightL_apply, Matrix.mul_assoc]
    rw [← e]
    exact h
  have hu : HasDerivAt (fun t : ℝ => rotGen * ((rotGL t).val * A))
      (rotGen * (rotGen * ((rotGL 0).val * A))) 0 := by
    have h : HasDerivAt (fun t : ℝ => rotGen * ((rotGL t).val * A))
        (mulLeftL rotGen (rotGen * ((rotGL 0).val * A))) 0 :=
      (mulLeftL rotGen).hasFDerivAt.comp_hasDerivAt 0 (hcurve 0)
    rw [← mulLeftL_apply rotGen (rotGen * ((rotGL 0).val * A))]
    exact h
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ (orbitMap F.val) ((rotGL t).val * A))
      (fderiv ℝ (fderiv ℝ (orbitMap F.val)) ((rotGL 0).val * A)
        (rotGen * ((rotGL 0).val * A))) 0 :=
    (hdiff' _ (hRA 0)).hasFDerivAt.comp_hasDerivAt 0 (hcurve 0)
  have hD : ∀ θ : ℝ, HasDerivAt (fun t => realRep k M.E (rotGL t) (orbitMap F.val A))
      (fderiv ℝ (orbitMap F.val) ((rotGL θ).val * A) (rotGen * ((rotGL θ).val * A))) θ := by
    intro θ
    have h := (hdiff _ (hRA θ)).hasFDerivAt.comp_hasDerivAt θ (hcurve θ)
    have hfun : (fun t => realRep k M.E (rotGL t) (orbitMap F.val A)) =
        fun t => orbitMap F.val ((rotGL t).val * A) :=
      funext fun t => realRep_rot_orbitMap F.val hA t
    rw [hfun]
    exact h
  have hderiv : deriv (fun t => realRep k M.E (rotGL t) (orbitMap F.val A)) =
      fun θ => fderiv ℝ (orbitMap F.val) ((rotGL θ).val * A) (rotGen * ((rotGL θ).val * A)) :=
    funext fun θ => (hD θ).deriv
  have h2 := hc.clm_apply hu
  have hR0 : (rotGL 0).val * A = A := by rw [rotGL_zero, Units.val_one, Matrix.one_mul]
  rw [hR0] at h2
  unfold secondRot
  rw [hderiv]
  exact h2.deriv

theorem contDiffOn_secondRotExpr (F : smoothSubmodule (bergmanRep M)) :
    ContDiffOn ℝ ⊤ (secondRotExpr F.val) detNeZero := by
  have hY := contDiffOn_orbitMap F
  have hY' : ContDiffOn ℝ ⊤ (fderiv ℝ (orbitMap F.val)) detNeZero :=
    hY.fderiv_of_isOpen isOpen_detNeZero (by simp)
  have hY'' := hY'.fderiv_of_isOpen isOpen_detNeZero (m := ⊤) (by simp)
  have hX : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ => rotGen * A) detNeZero :=
    (mulLeftL rotGen).contDiff.contDiffOn
  have hXX : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ => rotGen * (rotGen * A))
      detNeZero :=
    ((mulLeftL rotGen).comp (mulLeftL rotGen)).contDiff.contDiffOn
  exact ((hY''.clm_apply hX).clm_apply hX).add (hY'.clm_apply hXX)

/-! ### Analyticity of the realization -/

variable (M)

theorem realRep_apply_mem {U : Subgroup BinaryFiniteGL} {F : BergmanSpace k M.E}
    (hF : ∀ w, F w ∈ fixedSubmodule M.σ U) (r : GL (Fin 2) ℝ) (w : ℂ) :
    realRep k M.E r F w ∈ fixedSubmodule M.σ U := by
  by_cases hw : w.im = 0
  · rw [realRep_apply_of_im_eq_zero _ _ hw]
    exact Submodule.zero_mem _
  · rw [realRep_apply _ _ hw]
    exact Submodule.smul_mem _ _ (hF _)

/-- **Analyticity.** The realization of a smooth vector is real analytic along `GL₂(ℝ)`. -/
theorem realizeFun_scalarSmooth (hk : 6 ≤ k) (F : smoothSubmodule (bergmanRep M))
    (g : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → BinaryRealGL => realizeFun F (g * atInfinity (x 0))) := by
  have hU := level_isOpenCompact F
  have hFU : ∀ w, (F.val : BergmanSpace k M.E) w ∈ fixedSubmodule M.σ (level F) :=
    apply_mem_fixed (level_fixed F)
  obtain ⟨b, hb⟩ := exists_inner_secondRot M hU hk g
  have heq : ∀ A' ∈ {A' : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ | ∀ i, (A' i).det ≠ 0},
      realizeFun F (g * atInfinity (invertibleMatrix (A' 0))) =
        ⟪b, secondRotExpr F.val (A' 0)⟫_ℂ := by
    intro A' hA'
    rw [realizeFun_eq F hU hFU, ← realizeU_realRep M hU hFU,
      hb _ (realRep_apply_mem M hFU _) (isRotSmooth_realRep_of_smooth F _)]
    exact congrArg _ (secondRot_orbitMap F (hA' 0))
  unfold Smooth
  refine ContDiffOn.congr ?_ heq
  have hS : ContDiffOn ℝ ⊤ (fun A' : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      secondRotExpr F.val (A' 0)) {A' | ∀ i, (A' i).det ≠ 0} :=
    (contDiffOn_secondRotExpr F).comp
      (contDiff_apply (𝕜 := ℝ) (E := Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 1)).contDiffOn
      (fun A' hA' => hA' 0)
  exact ((innerSL ℂ b).restrictScalars ℝ).contDiff.comp_contDiffOn hS

end TernaryPeriodPolynomials.Regularity

end
