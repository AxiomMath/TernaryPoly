module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PrimitiveInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalytic

@[expose] public section


/-!
# Regularity of the real good-line transfer on the radical

For a scalar form `F` with `EichlerData n F` and `n ≥ 5`, consider the real good-line transfer of
the Eichler normal form on radical pairs, `(Y₁, Y₂) ↦ t(e^{Y₁}, e^{Y₂})`, tested against a fixed
functional. It is differentiable in `Y₂`. Along the axis `r eⱼ`, the second vertex of the
integrand moves only through the radical difference, so the normal form enters the `r`-derivative
at `r = 0` only through its values at the Levi point of `e^{Y₁}`. Hence the partial derivative
`Y₁ ↦ ∂_{Y₂ = eⱼ} t(e^{Y₁}, e^{Y₂})|_{Y₂ = 0}` is an integral of a family that is uniformly
Lipschitz in `Y₁` and `C¹` in `Y₁`, with derivatives bounded uniformly in the good-line
coordinate. It is therefore of class `C¹`, and its derivative at the origin is the integrated
mixed derivative of the radical section.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {F : BinaryAdelicGL → ℂ → ℂ}

/-! ### Smooth ingredients -/

/-- The derivative at `r = 0` of a `C²` function of `(x, r)` is `C¹` in `x`. -/
theorem contDiffAt_deriv_slice {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {R : X × ℝ → ℂ} {x₀ : X} (hR : ContDiffAt ℝ 2 R (x₀, 0)) :
    ContDiffAt ℝ 1 (fun x => deriv (fun r => R (x, r)) 0) x₀ := by
  have derivative := ContDiffAt.fderiv (f := fun (x : X) (r : ℝ) => R (x, r))
    (g := fun _ => (0 : ℝ)) (x₀ := x₀) (m := 1) hR contDiffAt_const (by norm_num)
  exact ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).contDiff.contDiffAt).comp x₀ derivative

/-- The first vertex `e^{x}` of the radical pair, as a family over `(x, r)`. -/
def pairFirst (p : (Fin 2 → ℝ) × ℝ) : LineGroup := lineRadicalElement p.1

/-- The second vertex `e^{x + r eⱼ}` of the radical pair, as a family over `(x, r)`. -/
def pairSecond (j : Fin 2) (p : (Fin 2 → ℝ) × ℝ) : LineGroup :=
  lineRadicalElement (p.1 + p.2 • Pi.single j 1)

theorem smoothLineFamily_pairFirst : SmoothLineFamily pairFirst :=
  smoothLineFamily_radical.comp contDiff_fst

theorem smoothLineFamily_pairSecond (j : Fin 2) : SmoothLineFamily (pairSecond j) :=
  smoothLineFamily_radical.comp (contDiff_fst.add (contDiff_snd.smul contDiff_const))

/-- The `r`-derivative at `r = 0` of the smooth part of the radical integrand. -/
def pairGamma (j : Fin 2) (m : Fin (Module.finrank ℂ (HomogeneousPoly n))) (j' : Fin (n + 2))
    (x : Matrix (Fin 3) (Fin 3) ℝ × (Fin 2 → ℝ)) : ℂ :=
  deriv (fun r => familyRadicalValue (n := n) pairFirst (pairSecond j) m j' (x.1, (x.2, r))) 0

theorem contDiffAt_pairGamma (j : Fin 2) (m : Fin (Module.finrank ℂ (HomogeneousPoly n)))
    (j' : Fin (n + 2)) {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k ∈ orthogonalMatrices)
    (x : Fin 2 → ℝ) : ContDiffAt ℝ 1 (pairGamma (n := n) j m j') (k, x) := by
  have smooth := contDiffAt_familyRadicalValue (n := n) smoothLineFamily_pairFirst
    (smoothLineFamily_pairSecond j) m j' hk (x, 0)
  have shuffle : ContDiff ℝ 2
      (fun y : (Matrix (Fin 3) (Fin 3) ℝ × (Fin 2 → ℝ)) × ℝ => (y.1.1, (y.1.2, y.2))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  exact contDiffAt_deriv_slice (smooth.comp ((k, x), (0 : ℝ)) shuffle.contDiffAt)

theorem hasDerivAt_pairValue (j : Fin 2) (m : Fin (Module.finrank ℂ (HomogeneousPoly n)))
    (j' : Fin (n + 2)) {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k ∈ orthogonalMatrices)
    (x : Fin 2 → ℝ) :
    HasDerivAt (fun r => familyRadicalValue (n := n) pairFirst (pairSecond j) m j' (k, (x, r)))
      (pairGamma j m j' (k, x)) 0 := by
  have smooth := contDiffAt_familyRadicalValue (n := n) smoothLineFamily_pairFirst
    (smoothLineFamily_pairSecond j) m j' hk (x, 0)
  have path : DifferentiableAt ℝ (fun r : ℝ => (k, (x, r))) 0 :=
    (differentiableAt_const _).prodMk ((differentiableAt_const x).prodMk differentiableAt_id)
  exact ((smooth.differentiableAt (by norm_num)).comp (0 : ℝ) path).hasDerivAt

/-- The coordinates of the normal form at the Levi point of `k · e^{x}`. -/
def radicalCoord (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h' : BinaryAdelicGL) (j' : Fin (n + 2))
    (x : Matrix (Fin 3) (Fin 3) ℝ × (Fin 2 → ℝ)) : ℂ :=
  (binaryWeightBasis (n + 1)).coord j' (eichlerPointNormal n F
    (movedPoint (fun Y : Fin 2 → ℝ => (lineMatrix (lineRadicalElement Y)).val) x) h')

theorem continuousOn_eichlerPointNormalDeriv
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) :
    ContinuousOn (fun z => eichlerPointNormalDeriv n F z h j) {z : ℂ | 0 < z.im} := by
  have kernel (h' : BinaryAdelicGL) (j' : Fin (n + 2)) :
      ContinuousOn (eichlerKernel n F h' j') {z : ℂ | 0 < z.im} :=
    (differentiableOn_eichlerKernel F holomorphic h' j').continuousOn
  have reflected (i : Fin (n + 2)) : ContinuousOn (fun z => eichlerKernel n F
      (h * atInfinity UpperHalfPlane.J) i (binaryComplexReflection z)) {z : ℂ | 0 < z.im} :=
    (kernel _ i).comp binaryComplexReflection.continuous.continuousOn
      fun z hz => binaryComplexReflection_mem hz
  unfold eichlerPointNormalDeriv
  exact ((((kernel h j).smul (continuousOn_const (c := ContinuousLinearMap.id ℝ ℂ))).add
    (continuousOn_finsetSum _ fun i _ => (continuousOn_const.mul (reflected i)).smul
      (continuousOn_const (c := binaryComplexReflection))))).const_smul
      ((2 : ℂ)⁻¹)

/-- The coordinates of the pointwise normal form are `C¹` on the upper half plane. -/
theorem contDiffAt_coord_eichlerPointNormal
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    ContDiffAt ℝ 1 (fun w => (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h))
      z :=
  contDiffAt_one_iff.mpr ⟨fun w => eichlerPointNormalDeriv n F w h j, {w | 0 < w.im},
    eichlerUpperSet_isOpen.mem_nhds hz, continuousOn_eichlerPointNormalDeriv holomorphic h j,
    fun _ hw => hasFDerivAt_coord_eichlerPointNormal F holomorphic hw h j⟩

theorem contDiffAt_radicalCoord (hF : EichlerData n F) (h' : BinaryAdelicGL) (j' : Fin (n + 2))
    {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k ∈ orthogonalMatrices) (x₀ : Fin 2 → ℝ) :
    ContDiffAt ℝ 1 (fun x => radicalCoord n F h' j' (k, x)) x₀ := by
  have hdet := det_mul_lineMatrix_ne_zero hk (lineRadicalElement x₀)
  have point : ContDiffAt ℝ 1
      (movedPoint (fun Y : Fin 2 → ℝ => (lineMatrix (lineRadicalElement Y)).val)) (k, x₀) :=
    contDiffAt_movedPoint contDiff_lineMatrix_radical hdet
  have pair : ContDiffAt ℝ 1 (fun x : Fin 2 → ℝ => (k, x)) x₀ :=
    contDiffAt_const.prodMk contDiffAt_id
  have upper := movedPoint_im_pos
    (L := fun Y : Fin 2 → ℝ => (lineMatrix (lineRadicalElement Y)).val) (x := (k, x₀)) hdet
  have composed := (contDiffAt_coord_eichlerPointNormal hF.holomorphic upper h' j').comp x₀
    (point.comp x₀ pair)
  exact composed

/-! ### The radical section along an axis -/

/-- The `r`-derivative at `r = 0` of the regular part of the radical section along `r eⱼ`. -/
def radicalSlope (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (u : ℝ × ℝ) (x : Fin 2 → ℝ) : ℂ :=
  ∑ j' : Fin (n + 2), ∑ m, radicalCoord n F (movedAdelic h u) j' ((gsOrth u).val, x) *
    testCoeff functional u m * pairGamma j m j' ((gsOrth u).val, x)

theorem radicalSection_axis_eq (u : ℝ × ℝ) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x : Fin 2 → ℝ) (r : ℝ) :
    radicalSection (eichlerNormal n F) u h functional x (r • Pi.single j 1) =
      transferScale n u * ∑ j' : Fin (n + 2), ∑ m,
        radicalCoord n F (movedAdelic h u) j' ((gsOrth u).val, x) * testCoeff functional u m *
          familyRadicalValue pairFirst (pairSecond j) m j' ((gsOrth u).val, (x, r)) := by
  unfold radicalSection
  rw [functional_relativeIntegrand]
  rfl

theorem hasDerivAt_radicalSection (u : ℝ × ℝ) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x : Fin 2 → ℝ) :
    HasDerivAt (fun r : ℝ => radicalSection (eichlerNormal n F) u h functional x
      (r • Pi.single j 1)) (transferScale n u * radicalSlope n F h functional j u x) 0 := by
  simp only [radicalSection_axis_eq]
  refine HasDerivAt.const_mul _ ?_
  unfold radicalSlope
  exact HasDerivAt.fun_sum fun j' _ => HasDerivAt.fun_sum fun m _ =>
    (hasDerivAt_pairValue j m j' (gsOrth_val_mem u) x).const_mul _

theorem aestronglyMeasurable_radicalSlope (hF : EichlerData n F) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x : Fin 2 → ℝ) :
    AEStronglyMeasurable (fun u => transferScale n u * radicalSlope n F h functional j u x)
      ((volume : Measure ℝ).prod volume) :=
  aestronglyMeasurable_of_hasDerivAt
    (f := fun r u => radicalSection (eichlerNormal n F) u h functional x (r • Pi.single j 1))
    (x₀ := 0) (fun r => (continuous_functional_relativeIntegrand hF (lineRadicalElement x)
      (lineRadicalElement (x + r • Pi.single j 1)) h functional).aestronglyMeasurable)
    (Eventually.of_forall fun u => hasDerivAt_radicalSection u h functional j x)

/-! ### The transfer on radical pairs -/

/-- The real good-line transfer on the radical pair `(e^{Y₁}, e^{Y₂})`, tested. -/
def radicalTransfer (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (Y₁ Y₂ : Fin 2 → ℝ) : ℂ :=
  ∫ u, radicalSection N u h functional Y₁ Y₂ ∂((volume : Measure ℝ).prod volume)

theorem lineTransferCochain_radical_eq
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (Y₁ Y₂ : Fin 2 → ℝ)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    lineTransferCochain N (lineRadicalElement Y₁) (lineRadicalElement Y₂) (h, functional) =
      radicalTransfer N h functional Y₁ Y₂ := by
  have add : lineRadicalElement Y₁ * lineRadicalElement Y₂ = lineRadicalElement (Y₁ + Y₂) :=
    (map_mul SemidirectProduct.inl (Multiplicative.ofAdd Y₁) (Multiplicative.ofAdd Y₂)).symm
  rw [lineTransferCochain_apply, add]
  rfl

theorem differentiable_radicalTransfer (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (x : Fin 2 → ℝ) :
    Differentiable ℝ (fun b => radicalTransfer (eichlerNormal n F) h functional x b) := fun b₀ =>
  (hasFDerivAt_transfer_family large hF (a := fun _ => lineRadicalElement x)
    (c := fun b => lineRadicalElement (x + b)) (SmoothLineFamily.const _)
    (smoothLineFamily_radical.comp (contDiff_const.add contDiff_id)) h functional
      b₀).differentiableAt

theorem hasDerivAt_radicalTransfer_axis (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x : Fin 2 → ℝ) :
    HasDerivAt (fun r : ℝ => radicalTransfer (eichlerNormal n F) h functional x
      (r • Pi.single j 1))
      (∫ u, transferScale n u * radicalSlope n F h functional j u x
        ∂((volume : Measure ℝ).prod volume)) 0 := by
  have first : SmoothLineFamily (fun _ : ℝ => lineRadicalElement x) := SmoothLineFamily.const _
  have second : SmoothLineFamily (fun r : ℝ => lineRadicalElement (x + r • Pi.single j 1)) :=
    smoothLineFamily_radical.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have result := hasDerivAt_integral_of_uniformLipOn (B := Metric.closedBall 0 1)
    (T := transferScale n)
    (f := fun u r => transferRegular n F h functional (lineRadicalElement x)
      (lineRadicalElement (x + r • Pi.single j 1)) u)
    (I := fun r u => radicalSection (eichlerNormal n F) u h functional x (r • Pi.single j 1))
    (Metric.closedBall_mem_nhds 0 one_pos) (integrable_norm_transferScale large)
    (fun r _ u => functional_relativeIntegrand F u (lineRadicalElement x)
      (lineRadicalElement (x + r • Pi.single j 1)) h functional)
    (uniformLipOn_transferRegular hF first second (isCompact_closedBall 0 1)
      (convex_closedBall 0 1) h functional)
    (fun r => (continuous_functional_relativeIntegrand hF (lineRadicalElement x)
      (lineRadicalElement (x + r • Pi.single j 1)) h functional).aestronglyMeasurable)
    (fun u => (hasDerivAt_radicalSection u h functional j x).differentiableAt)
  have equal (u : ℝ × ℝ) : deriv (fun r : ℝ => radicalSection (eichlerNormal n F) u h functional x
      (r • Pi.single j 1)) 0 = transferScale n u * radicalSlope n F h functional j u x :=
    (hasDerivAt_radicalSection u h functional j x).deriv
  simp only [equal] at result
  exact result

/-! ### Regularity of the partial derivative -/

/-- The partial derivative `∂_{Y₂ = eⱼ}` at `Y₂ = 0` of the tested transfer on radical pairs. -/
def radicalSlopeIntegral (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x : Fin 2 → ℝ) : ℂ :=
  ∫ u, transferScale n u * radicalSlope n F h functional j u x ∂((volume : Measure ℝ).prod volume)

theorem fderiv_radicalTransfer_apply (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x : Fin 2 → ℝ) :
    fderiv ℝ (fun b => radicalTransfer (eichlerNormal n F) h functional x b) 0 (Pi.single j 1) =
      radicalSlopeIntegral n F h functional j x := by
  have outer := (differentiable_radicalTransfer large hF h functional x 0).hasFDerivAt
  have line : HasDerivAt (fun r : ℝ => r • (Pi.single j 1 : Fin 2 → ℝ)) (Pi.single j 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j 1 : Fin 2 → ℝ)
  exact (outer.comp_hasDerivAt_of_eq (0 : ℝ) line (by simp)).unique
    (hasDerivAt_radicalTransfer_axis large hF h functional j x)

theorem uniformLipOn_radicalSlope (hF : EichlerData n F) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) {B : Set (Fin 2 → ℝ)}
    (hB : IsCompact B) (hconv : Convex ℝ B) :
    UniformLipOn (fun u x => radicalSlope n F h functional j u x) B := by
  unfold radicalSlope
  refine UniformLipOn.sum _ fun j' _ => UniformLipOn.sum _ fun m _ => ?_
  obtain ⟨D, hD⟩ := exists_bound_orthogonal_functional functional (homogeneousBasis n m)
  exact ((uniformLipOn_pointCoord hF smoothLineFamily_radical hB hconv j' (movedAdelic h)).mul
    (UniformLipOn.const (B := B) hD)).mul (uniformLipOn_orthogonal hB hconv fun k hk x _ =>
      contDiffAt_pairGamma j m j' hk x)

theorem contDiffAt_radicalSlope (hF : EichlerData n F) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (u : ℝ × ℝ) (x₀ : Fin 2 → ℝ) :
    ContDiffAt ℝ 1 (radicalSlope n F h functional j u) x₀ := by
  unfold radicalSlope
  refine ContDiffAt.sum fun j' _ => ContDiffAt.sum fun m _ => ?_
  exact ((contDiffAt_radicalCoord hF _ j' (gsOrth_val_mem u) x₀).mul contDiffAt_const).mul
    ((contDiffAt_pairGamma j m j' (gsOrth_val_mem u) x₀).comp x₀
      (contDiffAt_const.prodMk contDiffAt_id))

theorem exists_bound_fderiv_radicalSlope (hF : EichlerData n F) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x₀ : Fin 2 → ℝ) :
    ∃ C : ℝ, ∀ x ∈ Metric.ball x₀ 1, ∀ u,
      ‖fderiv ℝ (fun x => transferScale n u * radicalSlope n F h functional j u x) x‖ ≤
        C * ‖transferScale n u‖ := by
  obtain ⟨C, hC0, hC⟩ := (uniformLipOn_radicalSlope hF h functional j
    (isCompact_closedBall x₀ 1) (convex_closedBall x₀ 1)).lipschitzOnWith
  refine ⟨C, fun x hx u => ?_⟩
  rw [fderiv_const_mul ((contDiffAt_radicalSlope hF h functional j u x).differentiableAt
    (by norm_num)), norm_smul, mul_comm C]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := norm_fderiv_le_of_lipschitzOn ℝ (Metric.closedBall_mem_nhds_of_mem hx) (hC u).2
  rwa [Real.coe_toNNReal _ hC0] at this

theorem aestronglyMeasurable_fderiv_radicalSlope (hF : EichlerData n F) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) (x : Fin 2 → ℝ) :
    AEStronglyMeasurable
      (fun u => fderiv ℝ (fun x => transferScale n u * radicalSlope n F h functional j u x) x)
      ((volume : Measure ℝ).prod volume) :=
  aestronglyMeasurable_of_hasFDerivAt
    (f := fun x u => transferScale n u * radicalSlope n F h functional j u x) (x₀ := x)
    (fun x => aestronglyMeasurable_radicalSlope hF h functional j x)
    (Eventually.of_forall fun u => (((contDiffAt_radicalSlope hF h functional j u
      x).differentiableAt (by norm_num)).const_mul _).hasFDerivAt)

theorem hasFDerivAt_radicalSlopeIntegral (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2)
    (x₀ : Fin 2 → ℝ) :
    HasFDerivAt (radicalSlopeIntegral n F h functional j)
      (∫ u, fderiv ℝ (fun x => transferScale n u * radicalSlope n F h functional j u x) x₀
        ∂((volume : Measure ℝ).prod volume)) x₀ :=
  hasFDerivAt_integral_of_uniformLipOn (B := Metric.closedBall x₀ 1) (T := transferScale n)
    (f := fun u x => radicalSlope n F h functional j u x)
    (Metric.closedBall_mem_nhds x₀ one_pos) (integrable_norm_transferScale large)
    (fun _ _ _ => rfl) (uniformLipOn_radicalSlope hF h functional j (isCompact_closedBall x₀ 1)
      (convex_closedBall x₀ 1)) (fun x => aestronglyMeasurable_radicalSlope hF h functional j x)
    fun u => (contDiffAt_const.mul (contDiffAt_radicalSlope hF h functional j u
      x₀)).differentiableAt (by norm_num)

theorem continuous_fderiv_radicalSlopeIntegral (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) :
    Continuous (fun x₀ => ∫ u, fderiv ℝ (fun x => transferScale n u *
      radicalSlope n F h functional j u x) x₀ ∂((volume : Measure ℝ).prod volume)) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨C, hC⟩ := exists_bound_fderiv_radicalSlope hF h functional j x₀
  refine continuousAt_of_dominated (bound := fun u => C * ‖transferScale n u‖)
    (Eventually.of_forall fun x => aestronglyMeasurable_fderiv_radicalSlope hF h functional j x)
    ?_ ((integrable_norm_transferScale large).const_mul C) (Eventually.of_forall fun u => ?_)
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    exact Eventually.of_forall fun u => hC x hx u
  · exact ((contDiffAt_const.mul (contDiffAt_radicalSlope hF h functional j u x₀)).fderiv_right
      (m := 0) (by norm_num)).continuousAt

/-- **The partial derivative of the transfer on radical pairs is `C¹`.** -/
theorem contDiff_radicalSlopeIntegral (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) :
    ContDiff ℝ 1 (radicalSlopeIntegral n F h functional j) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨_, continuous_fderiv_radicalSlopeIntegral large hF h
    functional j, hasFDerivAt_radicalSlopeIntegral large hF h functional j⟩

/-! ### The mixed derivative at the origin -/

theorem radicalMixed_eq (hF : EichlerData n F) (u : ℝ × ℝ) (i j : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    radicalMixed (eichlerNormal n F) u i j h functional =
      fderiv ℝ (fun x => transferScale n u * radicalSlope n F h functional j u x) 0
        (Pi.single i 1) := by
  unfold radicalMixed
  have inner : (fun s : ℝ => deriv (fun r : ℝ => radicalSection (eichlerNormal n F) u h
      functional (s • Pi.single i 1) (r • Pi.single j 1)) 0) =
      fun s => transferScale n u * radicalSlope n F h functional j u (s • Pi.single i 1) :=
    funext fun s => (hasDerivAt_radicalSection u h functional j _).deriv
  rw [inner]
  have outer := (((contDiffAt_const (c := transferScale n u)).mul
    (contDiffAt_radicalSlope hF h functional j u 0)).differentiableAt (by norm_num)).hasFDerivAt
  have line : HasDerivAt (fun s : ℝ => s • (Pi.single i 1 : Fin 2 → ℝ)) (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 2 → ℝ)
  exact (outer.comp_hasDerivAt_of_eq (0 : ℝ) line (by simp)).deriv

theorem integrable_fderiv_radicalSlope (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (j : Fin 2) :
    Integrable (fun u => fderiv ℝ (fun x => transferScale n u *
      radicalSlope n F h functional j u x) 0) ((volume : Measure ℝ).prod volume) := by
  obtain ⟨C, hC⟩ := exists_bound_fderiv_radicalSlope hF h functional j 0
  exact ((integrable_norm_transferScale large).const_mul C).mono'
    (aestronglyMeasurable_fderiv_radicalSlope hF h functional j 0)
    (Eventually.of_forall fun u => hC 0 (Metric.mem_ball_self one_pos) u)

theorem integrable_radicalMixed (large : 5 ≤ n) (hF : EichlerData n F) (i j : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => radicalMixed (eichlerNormal n F) u i j h functional)
      ((volume : Measure ℝ).prod volume) := by
  simp only [radicalMixed_eq hF]
  exact (ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1 : Fin 2 → ℝ)).integrable_comp
    (integrable_fderiv_radicalSlope large hF h functional j)

/-- **The derivative at the origin of the partial derivative is the integrated mixed
derivative of the radical section.** -/
theorem fderiv_radicalSlopeIntegral_apply (large : 5 ≤ n) (hF : EichlerData n F) (i j : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    fderiv ℝ (radicalSlopeIntegral n F h functional j) 0 (Pi.single i 1) =
      ∫ u, radicalMixed (eichlerNormal n F) u i j h functional
        ∂((volume : Measure ℝ).prod volume) := by
  rw [(hasFDerivAt_radicalSlopeIntegral large hF h functional j 0).fderiv,
    ContinuousLinearMap.integral_apply (integrable_fderiv_radicalSlope large hF h functional j)]
  simp only [radicalMixed_eq hF]

end TernaryPeriodPolynomials.AnalyticClasses
