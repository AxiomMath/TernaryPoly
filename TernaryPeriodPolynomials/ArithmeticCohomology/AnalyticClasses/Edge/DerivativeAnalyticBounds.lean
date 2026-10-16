module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticSmooth

@[expose] public section


/-!
# Uniform regularity of the transferred integrand of the Eichler normal form

For a scalar form `F` with `EichlerData n F`, a scalar test of the transferred integrand of the
pointwise Eichler normal form `N` at a simplex `(1, a, c)` of the real good-line stabilizer is
`s(u) · Σ_{j,m} N_j(z_a) · ℓ_u(e_m) · ω_{m,j}(x_a, x_c - x_a)`: here `s(u)` is the transfer scale,
`N_j` are the weight-basis coordinates of the pointwise normal form at the Levi point `z_a` of
`k(u) · lineMatrix a`, `ℓ_u = ℓ ∘ ρ(k(u)⁻¹)`, `ω_{m,j}` are the smooth scalar tests of the
canonical cochain and `x_q` is the radical coordinate of `k(u) · lineMatrix q`. Only the
orthogonal factor `k(u)` depends on `u`, so for smooth families `a(p), c(p)` the regular part is
bounded and Lipschitz near any `p₀`, uniformly in `u`, while `‖s‖` is integrable for `n ≥ 5`.
Hence the transfer integral of such families is differentiable, with the derivative under the
integral.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl
open TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ} {F : BinaryAdelicGL → ℂ → ℂ}

/-! ### The transfer scale -/

theorem norm_transferScale (u : ℝ × ℝ) :
    ‖transferScale n u‖ = kernelBase u ^ (-(((n : ℝ) + 3) / 4)) := by
  have form : GoodLineForm (standardGoodLineRealArgument u) := by
    simpa using goodLineForm_lineMatrix u 1
  set X := standardGoodLineRealArgument u
  set s := (cornerScale (gsVertex X) : ℝ) with hs
  have spos : 0 < s := cornerScale_pos _
  have first : ‖normPower (GeneralLinearGroup.det (atInfinity (gsPlaneVertex X).right))
      (((n : ℂ) + 3) / 2)‖ = (s ^ 3) ^ (((n : ℝ) + 3) / 2) := by
    have exponent : ((n : ℂ) + 3) / 2 = ((((n : ℝ) + 3) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [exponent, norm_normPower_det_atInfinity, abs_det_gsPlaneVertex_right form]
  have second : ‖((s : ℂ))⁻¹ ^ (n + 3)‖ = (s⁻¹) ^ (n + 3) := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg spos.le]
  have corner : s = (gsRadius u)⁻¹ := by
    rw [hs, cornerScale_gsVertex form, gsVertex_standard, gsUpper_corner]
  unfold transferScale
  rw [norm_mul, first, second, scale_exponent s spos, corner,
    ← abs_of_pos (inv_pos.mpr (gsRadius_pos u)), gsRadius_inv_rpow]
  congr 1
  ring

/-- **The transfer scale is absolutely integrable** for `n ≥ 5`. -/
theorem integrable_norm_transferScale (large : 5 ≤ n) :
    Integrable (fun u => ‖transferScale n u‖) ((volume : Measure ℝ).prod volume) := by
  simp only [norm_transferScale]
  exact kernelBase_decay_integrable large

/-! ### The relative integrand in coordinates -/

/-- The adelic argument `h · A(u)` of the relative integrand. -/
def movedAdelic (h : BinaryAdelicGL) (u : ℝ × ℝ) : BinaryAdelicGL :=
  h * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u)).right

/-- The regular part of a scalar test of the relative integrand of the Eichler normal form. -/
def transferRegular (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (a c : LineGroup) (u : ℝ × ℝ) : ℂ :=
  ∑ j : Fin (n + 2), ∑ m, (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F
      (symmetricPoint ((gsOrth u).val * (lineMatrix a).val)) (movedAdelic h u)) *
    functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ (homogeneousBasis n m)) *
    radicalValue n ((homogeneousBasis n).coord m) (binaryWeightBasis (n + 1) j)
      (symmetricRadical ((gsOrth u).val * (lineMatrix a).val))
      (symmetricRadical ((gsOrth u).val * (lineMatrix c).val) -
        symmetricRadical ((gsOrth u).val * (lineMatrix a).val))

/-- A scalar test of a linear image of a binary form, in the weight basis and the ternary basis. -/
theorem functional_linear_expand (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (Φ : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    functional (Φ Q) = ∑ j : Fin (n + 2), ∑ m, (binaryWeightBasis (n + 1)).coord j Q *
      functional (homogeneousBasis n m) *
        (homogeneousBasis n).coord m (Φ (binaryWeightBasis (n + 1) j)) := by
  conv_lhs => rw [← (binaryWeightBasis (n + 1)).sum_repr Q]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [functional_eq_basis_sum functional (Φ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Module.Basis.coord_apply]
  ring

/-- **A scalar test of the relative integrand of the Eichler normal form in coordinates.** -/
theorem functional_relativeIntegrand (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (a c : LineGroup)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (relativeIntegrand (eichlerNormal n F) u a c h) =
      transferScale n u * transferRegular n F h functional a c u := by
  have left : (relativeVertex u a).left =
      Multiplicative.ofAdd (symmetricRadical ((gsOrth u).val * (lineMatrix a).val)) := by
    rw [← relativeVertex_left]
    rfl
  have difference : (relativeVertex u a).left⁻¹ * (relativeVertex u c).left =
      Multiplicative.ofAdd (symmetricRadical ((gsOrth u).val * (lineMatrix c).val) -
        symmetricRadical ((gsOrth u).val * (lineMatrix a).val)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, relativeVertex_left, relativeVertex_left, toAdd_ofAdd]
    abel
  have normal : eichlerNormal n F (relativeVertex u a).right (movedAdelic h u) =
      eichlerPointNormal n F (symmetricPoint ((gsOrth u).val * (lineMatrix a).val))
        (movedAdelic h u) := by
    rw [eichlerNormal_eq_eichlerPointNormal, basePoint_relativeVertex_right]
  unfold relativeIntegrand
  rw [map_smul, smul_eq_mul, pointCanonical_relative]
  change _ * functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
    ((realUpperRadicalRep n).ρ (relativeVertex u a).left
      (realUpperBinaryValue n ((relativeVertex u a).left⁻¹ * (relativeVertex u c).left)
        (eichlerNormal n F (relativeVertex u a).right (movedAdelic h u))))) = _
  rw [difference, left, normal]
  congr 1
  exact functional_linear_expand (functional ∘ₗ realCoefficientComponent n trivialCharacter
    (gsOrth u)⁻¹) ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd
      (symmetricRadical ((gsOrth u).val * (lineMatrix a).val))) ∘ₗ realUpperBinaryValue n
        (Multiplicative.ofAdd (symmetricRadical ((gsOrth u).val * (lineMatrix c).val) -
          symmetricRadical ((gsOrth u).val * (lineMatrix a).val)))) _

theorem relativeIntegrand_eq_lineTransferIntegrand
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (a c : LineGroup) (h : BinaryAdelicGL) :
    relativeIntegrand N u a c h = lineTransferIntegrand N ![1, a, c] u h :=
  (lineTransferIntegrand_eq_relative N u a c h).symm

/-- Scalar tests of the relative integrand are continuous in the good-line coordinate. -/
theorem continuous_functional_relativeIntegrand (hF : EichlerData n F) (a c : LineGroup)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun u => functional (relativeIntegrand (eichlerNormal n F) u a c h)) := by
  simp only [relativeIntegrand_eq_lineTransferIntegrand]
  exact lineTransferIntegrand_continuous hF.pointCocycle ![1, a, c] h functional

/-- Scalar tests of the relative integrand are integrable in the good-line coordinate. -/
theorem integrable_functional_relativeIntegrand (large : 5 ≤ n) (hF : EichlerData n F)
    (a c : LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => functional (relativeIntegrand (eichlerNormal n F) u a c h))
      ((volume : Measure ℝ).prod volume) := by
  simp only [relativeIntegrand_eq_lineTransferIntegrand]
  exact lineTransferIntegrand_integrable large hF.pointCocycle ![1, a, c] h functional

/-! ### Uniform regularity -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
theorem UniformLipOn.reindex {ι κ : Type*} {f : ι → P → ℂ} {B : Set P} (hf : UniformLipOn f B)
    (σ : κ → ι) : UniformLipOn (fun k => f (σ k)) B := by
  obtain ⟨C, hC0, hC⟩ := hf
  exact ⟨C, hC0, fun k => hC (σ k)⟩

/-- A jointly `C¹` function of an orthogonal matrix and a parameter, evaluated at the orthogonal
Gram–Schmidt factor, is uniformly Lipschitz in the parameter. -/
theorem uniformLipOn_orthogonal {f : Matrix (Fin 3) (Fin 3) ℝ × P → ℂ} {B : Set P}
    (hB : IsCompact B) (hconv : Convex ℝ B)
    (smooth : ∀ k ∈ orthogonalMatrices, ∀ p ∈ B, ContDiffAt ℝ 1 f (k, p)) :
    UniformLipOn (fun (u : ℝ × ℝ) p => f ((gsOrth u).val, p)) B :=
  (uniformLipOn_of_contDiffAt orthogonalMatrices_isCompact hB hconv smooth).reindex
    (fun u => ⟨(gsOrth u).val, gsOrth_val_mem u⟩)

/-- The scalar tests `ℓ_u(e_m)` are bounded uniformly in `u`. -/
theorem exists_bound_orthogonal_functional (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (v : HomogeneousPoly n) :
    ∃ D : ℝ, ∀ u : ℝ × ℝ,
      ‖functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ v)‖ ≤ D := by
  have continuity := realCoefficientComponent_functional_continuous (fun k : RealGL3 => k)
    continuous_id v functional
  obtain ⟨D, hD⟩ := realOrthogonalSet_isCompact.exists_bound_of_continuousOn
    continuity.continuousOn
  exact ⟨D, fun u => hD _ (gsOrth_inv_mem u)⟩

/-- A smooth family of elements of the real good-line stabilizer. -/
def SmoothLineFamily (a : P → LineGroup) : Prop :=
  ContDiff ℝ 2 (fun p => (lineMatrix (a p)).val)

/-- **The coordinates of the normal form at the moved Levi points are uniformly Lipschitz.** -/
theorem uniformLipOn_pointCoord (hF : EichlerData n F) {a : P → LineGroup}
    (ha : SmoothLineFamily a) {B : Set P} (hB : IsCompact B) (hconv : Convex ℝ B)
    (j : Fin (n + 2)) (index : ℝ × ℝ → BinaryAdelicGL) :
    UniformLipOn (fun u p => (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F
      (movedPoint (fun p => (lineMatrix (a p)).val) ((gsOrth u).val, p)) (index u))) B := by
  set L := fun p => (lineMatrix (a p)).val
  have hL1 : ContDiff ℝ 1 L := ha.of_le (by norm_num)
  have smooth : ∀ k ∈ orthogonalMatrices, ∀ p ∈ B, ContDiffAt ℝ 1 (movedPoint L) (k, p) :=
    fun k hk p _ => contDiffAt_movedPoint hL1 (det_mul_lineMatrix_ne_zero hk (a p))
  set S := movedPoint L '' (orthogonalMatrices ×ˢ B)
  have compact : IsCompact S := (orthogonalMatrices_isCompact.prod hB).image_of_continuousOn
    fun x hx => (smooth x.1 hx.1 x.2 hx.2).continuousAt.continuousWithinAt
  have upper : S ⊆ {z : ℂ | 0 < z.im} := by
    rintro _ ⟨x, hx, rfl⟩
    exact movedPoint_im_pos (det_mul_lineMatrix_ne_zero hx.1 (a x.2))
  obtain ⟨K, hSK, -, hK, hKc, hKconv⟩ := exists_convex_compact_upper compact upper
  obtain ⟨D, hD0, hD⟩ := hF.coord_lipschitz hK hKc hKconv j
  obtain ⟨C, hC⟩ := hF.coord_bounded hKc hK j
  have z := uniformLipOn_orthogonal hB hconv smooth
  refine UniformLipOn.comp (K := K) (index := index) (g := fun h' w =>
    (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h')) z
    (fun u p hp => hSK ⟨((gsOrth u).val, p), ⟨gsOrth_val_mem u, hp⟩, rfl⟩)
    ⟨max D C, le_trans hD0 (le_max_left _ _), fun h' w hw => ⟨(hC h' w hw).trans
      (le_max_right _ _), fun w' hw' => (hD h' w' hw' w hw).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩⟩

/-- The smooth part of the regular part, as a function of the orthogonal matrix and the
parameter. -/
def familyRadicalValue (a c : P → LineGroup) (m : Fin (Module.finrank ℂ (HomogeneousPoly n)))
    (j : Fin (n + 2)) (x : Matrix (Fin 3) (Fin 3) ℝ × P) : ℂ :=
  radicalValue n ((homogeneousBasis n).coord m) (binaryWeightBasis (n + 1) j)
    (movedRadical (fun p => (lineMatrix (a p)).val) x)
    (movedRadical (fun p => (lineMatrix (c p)).val) x -
      movedRadical (fun p => (lineMatrix (a p)).val) x)

theorem contDiffAt_familyRadicalValue {a c : P → LineGroup} (ha : SmoothLineFamily a)
    (hc : SmoothLineFamily c) (m : Fin (Module.finrank ℂ (HomogeneousPoly n))) (j : Fin (n + 2))
    {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k ∈ orthogonalMatrices) (p : P) :
    ContDiffAt ℝ 2 (familyRadicalValue (n := n) a c m j) (k, p) := by
  have ra : ContDiffAt ℝ 2 (movedRadical (fun p => (lineMatrix (a p)).val)) (k, p) :=
    contDiffAt_movedRadical ha (det_mul_lineMatrix_ne_zero hk (a p))
  have rc : ContDiffAt ℝ 2 (movedRadical (fun p => (lineMatrix (c p)).val)) (k, p) :=
    contDiffAt_movedRadical hc (det_mul_lineMatrix_ne_zero hk (c p))
  have outer : ContDiff ℝ 2 (fun xy : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      radicalValue n ((homogeneousBasis n).coord m) (binaryWeightBasis (n + 1) j) xy.1 xy.2) :=
    contDiff_radicalValue _ _
  have composed := outer.contDiffAt.comp (k, p) (ra.prodMk (rc.sub ra))
  exact composed

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem transferRegular_family (a c : P → LineGroup) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ) (p : P) :
    transferRegular n F h functional (a p) (c p) u =
      ∑ j : Fin (n + 2), ∑ m, (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F
        (movedPoint (fun p => (lineMatrix (a p)).val) ((gsOrth u).val, p)) (movedAdelic h u)) *
      functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
        (homogeneousBasis n m)) * familyRadicalValue a c m j ((gsOrth u).val, p) :=
  rfl

/-- **The regular part of a smooth family is uniformly Lipschitz.** -/
theorem uniformLipOn_transferRegular (hF : EichlerData n F) {a c : P → LineGroup}
    (ha : SmoothLineFamily a) (hc : SmoothLineFamily c) {B : Set P} (hB : IsCompact B)
    (hconv : Convex ℝ B) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    UniformLipOn (fun u p => transferRegular n F h functional (a p) (c p) u) B := by
  simp only [transferRegular_family]
  refine UniformLipOn.sum _ fun j _ => UniformLipOn.sum _ fun m _ => ?_
  obtain ⟨D, hD⟩ := exists_bound_orthogonal_functional functional (homogeneousBasis n m)
  exact ((uniformLipOn_pointCoord hF ha hB hconv j (movedAdelic h)).mul
    (UniformLipOn.const (B := B) hD)).mul (uniformLipOn_orthogonal hB hconv fun k hk p _ =>
      (contDiffAt_familyRadicalValue ha hc m j hk p).of_le (by norm_num))

theorem differentiableAt_pointCoord (hF : EichlerData n F) {a : P → LineGroup}
    (ha : SmoothLineFamily a) (j : Fin (n + 2)) (h' : BinaryAdelicGL)
    {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k ∈ orthogonalMatrices) (p₀ : P) :
    DifferentiableAt ℝ (fun p => (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F
      (movedPoint (fun p => (lineMatrix (a p)).val) (k, p)) h')) p₀ := by
  have hdet := det_mul_lineMatrix_ne_zero hk (a p₀)
  have point : ContDiffAt ℝ 2 (movedPoint (fun p => (lineMatrix (a p)).val)) (k, p₀) :=
    contDiffAt_movedPoint ha hdet
  have pair : DifferentiableAt ℝ (fun p : P => (k, p)) p₀ :=
    (differentiableAt_const k).prodMk differentiableAt_id
  have inner : DifferentiableAt ℝ (fun p => movedPoint (fun p => (lineMatrix (a p)).val) (k, p))
      p₀ :=
    (point.differentiableAt (by norm_num)).comp p₀ pair
  have upper : 0 < (movedPoint (fun p => (lineMatrix (a p)).val) (k, p₀)).im :=
    movedPoint_im_pos (L := fun p => (lineMatrix (a p)).val) (x := (k, p₀)) hdet
  have composed := (hasFDerivAt_coord_eichlerPointNormal F hF.holomorphic upper
    h' j).differentiableAt.comp p₀ inner
  exact composed

theorem differentiableAt_transferRegular (hF : EichlerData n F) {a c : P → LineGroup}
    (ha : SmoothLineFamily a) (hc : SmoothLineFamily c) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ) (p₀ : P) :
    DifferentiableAt ℝ (fun p => transferRegular n F h functional (a p) (c p) u) p₀ := by
  simp only [transferRegular_family]
  refine DifferentiableAt.fun_sum fun j _ => DifferentiableAt.fun_sum fun m _ => ?_
  refine ((differentiableAt_pointCoord hF ha j _ (gsOrth_val_mem u) p₀).mul
    (differentiableAt_const _)).mul ?_
  exact ((contDiffAt_familyRadicalValue ha hc m j (gsOrth_val_mem u) p₀).differentiableAt
    (by norm_num)).comp p₀ (differentiableAt_const _ |>.prodMk differentiableAt_id)

/-- **Differentiation of the transfer integral of a smooth family under the integral sign.** -/
theorem hasFDerivAt_transfer_family [FiniteDimensional ℝ P] (large : 5 ≤ n)
    (hF : EichlerData n F) {a c : P → LineGroup} (ha : SmoothLineFamily a)
    (hc : SmoothLineFamily c) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (p₀ : P) :
    HasFDerivAt (fun p => ∫ u, functional (relativeIntegrand (eichlerNormal n F) u (a p) (c p) h)
        ∂((volume : Measure ℝ).prod volume))
      (∫ u, fderiv ℝ (fun p => functional (relativeIntegrand (eichlerNormal n F) u (a p) (c p) h))
        p₀ ∂((volume : Measure ℝ).prod volume)) p₀ := by
  have := FiniteDimensional.proper_real P
  refine hasFDerivAt_integral_of_uniformLipOn (B := Metric.closedBall p₀ 1)
    (T := transferScale n) (Metric.closedBall_mem_nhds p₀ one_pos)
    (integrable_norm_transferScale large)
    (fun p _ u => functional_relativeIntegrand F u (a p) (c p) h functional)
    (uniformLipOn_transferRegular hF ha hc (isCompact_closedBall p₀ 1) (convex_closedBall p₀ 1)
      h functional)
    (fun p => (continuous_functional_relativeIntegrand hF (a p) (c p) h
      functional).aestronglyMeasurable) fun u => ?_
  simp only [functional_relativeIntegrand]
  exact (differentiableAt_transferRegular hF ha hc h functional u p₀).const_mul _

end TernaryPeriodPolynomials.AnalyticClasses
