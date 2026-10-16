module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.BridgeTransferAlgebra

@[expose] public section


/-!
# Integrability of the real transfer of a binary coboundary

Let `κ : GL₂(𝔸) → Sym^{n+1}` have uniformly bounded scalar tests and continuous translates
`A ↦ λ(A · κ)(h)`. Then, for `n ≥ 5`, the transferred integrand of the constant family `κ` at every
degenerate simplex `(y, y, z)` of the real good-line stabilizer is absolutely integrable over the
good-line coordinate. The bound is the one of the transferred canonical integrand, which only uses
bounds on compact sets of the binary family; continuity follows from the identity
`Q₀ · θκ (Q₀⁻¹ Q₁) = Canon(δκ)(Q₀, Q₀⁻¹ Q₁) + θκ (Q₁) - θκ (Q₀)`, whose terms are continuous at a
fixed adelic point. Consequently the transfer of the canonical cochain of `δκ` is the coboundary
of the transfer of `θκ`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl
open TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ}

/-! ### Bounds for families bounded on compact sets -/

/-- **Uniform bound of the canonical cochain on compact sets of plane matrices**, for a binary
family whose scalar tests are bounded on compact sets uniformly in the adelic point. -/
theorem pointCanonical_shape_bound_of
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ (K : Set BinaryRealGL), IsCompact K →
      ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
        ∃ C : ℝ, ∀ A ∈ K, ∀ h, ‖functional (N A h)‖ ≤ C)
    {w₁ w₂ : RealGL3} {a₁ b₁ a₂ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M₁ ∈ shapeSet w₁ a₁ b₁, ∀ M₂ ∈ shapeSet w₂ a₂ b₂, ∀ h,
      ‖functional (pointCanonical N (matrixPlanePoint M₁) (matrixPlanePoint M₂) h)‖ ≤ C := by
  set K₁ := shapeSet w₁ a₁ b₁
  set K₂ := shapeSet w₂ a₂ b₂
  have compact₁ : CompactSpace K₁ := isCompact_iff_compactSpace.mp (shapeSet_isCompact _ _ _)
  have compact₂ : CompactSpace K₂ := isCompact_iff_compactSpace.mp (shapeSet_isCompact _ _ _)
  have plane₁ := shapeSet_planeContinuous (w := w₁) (b := b₁) ha₁
  have plane₂ := shapeSet_planeContinuous (w := w₂) (b := b₂) ha₂
  have leviCompact : IsCompact (Set.range fun M : K₁ => (matrixPlanePoint M.val).right) :=
    isCompact_range plane₁.2
  have coordinate (j : _) := bounded _ leviCompact ((binaryBasis n).coord j)
  choose C hC using coordinate
  have operator (j : _) : ∃ D : ℝ, ∀ M₁ : K₁, ∀ M₂ : K₂,
      ‖functional ((realUpperRadicalRep n).ρ (matrixPlanePoint M₁.val).left
        (realUpperBinaryValue n (realPlaneRadicalAction (matrixPlanePoint M₁.val).right
          (matrixPlanePoint M₂.val).left) (binaryBasis n j)))‖ ≤ D := by
    have continuity : Continuous (fun pair : K₁ × K₂ =>
        functional ((realUpperRadicalRep n).ρ (matrixPlanePoint pair.1.val).left
          (realUpperBinaryValue n (realPlaneRadicalAction (matrixPlanePoint pair.1.val).right
            (matrixPlanePoint pair.2.val).left) (binaryBasis n j)))) := by
      let basis := homogeneousBasis n
      have expand (pair : K₁ × K₂) :
          functional ((realUpperRadicalRep n).ρ (matrixPlanePoint pair.1.val).left
            (realUpperBinaryValue n (realPlaneRadicalAction (matrixPlanePoint pair.1.val).right
              (matrixPlanePoint pair.2.val).left) (binaryBasis n j))) =
          ∑ i, basis.coord i (realUpperBinaryValue n (realPlaneRadicalAction
              (matrixPlanePoint pair.1.val).right (matrixPlanePoint pair.2.val).left)
              (binaryBasis n j)) *
            functional ((realUpperRadicalRep n).ρ (matrixPlanePoint pair.1.val).left
              (basis i)) := by
        conv_lhs => rw [← basis.sum_repr (realUpperBinaryValue n _ (binaryBasis n j))]
        simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
      simp_rw [expand]
      apply continuous_finsetSum
      intro i _
      apply Continuous.mul
      · exact realUpperBinaryValue_functional_continuous
          (continuous_radicalAction (plane₁.2.comp continuous_fst)
            ((plane₂.1.comp continuous_snd))) _ _
      · rw [show (fun pair : K₁ × K₂ => functional ((realUpperRadicalRep n).ρ
            (matrixPlanePoint pair.1.val).left (basis i))) = fun pair : K₁ × K₂ =>
            functional (realCoefficientComponent n trivialCharacter
              (realPlaneMatrix (SemidirectProduct.inl (matrixPlanePoint pair.1.val).left))
              (basis i)) by
              funext pair; rw [realPlaneMatrix_inl]; rfl]
        exact realCoefficientComponent_functional_continuous _
          ((planeContinuous_inlRadical (plane₁.1.comp continuous_fst)).matrix) _ _
    obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn continuity.norm.continuousOn
    exact ⟨D, fun M₁ M₂ => by
      have := hD (M₁, M₂) (Set.mem_univ _)
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at this⟩
  choose D hD using operator
  refine ⟨∑ j, |C j| * |D j|, Finset.sum_nonneg (fun j _ => by positivity),
    fun M₁ hM₁ M₂ hM₂ h => ?_⟩
  rw [pointCanonical_expand, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [map_smul, smul_eq_mul, norm_mul]
  apply mul_le_mul
  · exact (hC j _ ⟨⟨M₁, hM₁⟩, rfl⟩ h).trans (le_abs_self _)
  · exact (hD j ⟨M₁, hM₁⟩ ⟨M₂, hM₂⟩).trans (le_abs_self _)
  · exact norm_nonneg _
  · exact abs_nonneg _

/-- **Uniform bound of the transferred integrand**, for a binary family whose scalar tests are
bounded on compact sets uniformly in the adelic point. -/
theorem lineTransferIntegrand_bound_of
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ (K : Set BinaryRealGL), IsCompact K →
      ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
        ∃ C : ℝ, ∀ A ∈ K, ∀ h, ‖functional (N A h)‖ ≤ C)
    (x : Fin 3 → LineGroup) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (h : BinaryAdelicGL),
      ‖functional (lineTransferIntegrand N x u h)‖ ≤
        (cornerScale (gsVertex (standardGoodLineRealArgument u * lineMatrix (x 0))) : ℝ) ^
          (((n : ℝ) + 3) / 2) * C := by
  obtain ⟨B, hB0, hB⟩ := functional_coefficient_bound (n := n) (lineMatrix (x 0)) functional
  set w₁ := (lineMatrix (x 0))⁻¹ * lineMatrix (x 1)
  set w₂ := (lineMatrix (x 1))⁻¹ * lineMatrix (x 2)
  have positive (w : RealGL3) : 0 < (Real.sqrt (frobeniusSq w))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (frobeniusSq_pos _))
  have bounds (m : Fin 3 →₀ ℕ) := pointCanonical_shape_bound_of bounded (w₁ := w₁)
    (b₁ := Real.sqrt (frobeniusSq ((lineMatrix (x 1))⁻¹ * lineMatrix (x 0)))) (w₂ := w₂)
    (b₂ := Real.sqrt (frobeniusSq ((lineMatrix (x 2))⁻¹ * lineMatrix (x 1))))
    (positive w₁) (positive w₂) (coeffFunctional m)
  choose C hC0 hC using bounds
  refine ⟨∑ m ∈ degreeMonomials n, B m * C m,
    Finset.sum_nonneg (fun m _ => mul_nonneg (hB0 m) (hC0 m)), fun u h => ?_⟩
  set X := standardGoodLineRealArgument u * lineMatrix (x 0)
  set s := (cornerScale (gsVertex X) : ℝ) with hs
  have spos : 0 < s := cornerScale_pos _
  rw [lineTransferIntegrand_apply, map_smul, smul_eq_mul, norm_mul, norm_mul]
  set Y := pointCanonical N ((gsPlaneVertex X)⁻¹ *
      gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 1)))
    ((gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 1)))⁻¹ *
      gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 2)))
    (h * atInfinity (gsPlaneVertex X).right)
  have first : ‖normPower (GeneralLinearGroup.det (atInfinity (gsPlaneVertex X).right))
      (((n : ℂ) + 3) / 2)‖ = (s ^ 3) ^ (((n : ℝ) + 3) / 2) := by
    have exponent : ((n : ℂ) + 3) / 2 = ((((n : ℝ) + 3) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [exponent, norm_normPower_det_atInfinity,
      abs_det_gsPlaneVertex_right (goodLineForm_lineMatrix u (x 0))]
  have second : ‖((s : ℂ))⁻¹ ^ (n + 3)‖ = (s⁻¹) ^ (n + 3) := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg spos.le]
  have coefficient (m : Fin 3 →₀ ℕ) : ‖Y.val.coeff m‖ ≤ C m := by
    have member₁ := edgeArgument_mem (lineMatrix (x 0)) (lineMatrix (x 1)) u
      (goodLineForm_lineMatrix u (x 0)) (goodLineForm_lineMatrix u (x 1))
    have member₂ := edgeArgument_mem (lineMatrix (x 1)) (lineMatrix (x 2)) u
      (goodLineForm_lineMatrix u (x 1)) (goodLineForm_lineMatrix u (x 2))
    have bound := hC m _ member₁ _ member₂ (h * atInfinity (gsPlaneVertex X).right)
    rw [matrixPlanePoint_realPlaneMatrix, matrixPlanePoint_realPlaneMatrix,
      coeffFunctional_apply] at bound
    exact bound
  have third : ‖functional (realCoefficientComponent n trivialCharacter
      (lineMatrix (x 0) * (gsOrth (gsChart X))⁻¹) Y)‖ ≤ ∑ m ∈ degreeMonomials n, B m * C m :=
    (hB _ (gsOrth_inv_mem _) Y).trans (Finset.sum_le_sum (fun m _ =>
      mul_le_mul_of_nonneg_left (coefficient m) (hB0 m)))
  rw [first, second, scale_exponent s spos]
  exact mul_le_mul_of_nonneg_left third (Real.rpow_nonneg spos.le _)

/-! ### Continuity at a fixed adelic point -/

/-- Scalar tests of coefficient-moved canonical values along continuous paths are continuous,
for a binary family whose scalar tests are continuous in the matrix. -/
theorem pointCanonical_moved_continuous_of
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (N A h)))
    {X : Type} [TopologicalSpace X] {p q : X → RealPlaneGroup} (hp : PlaneContinuous p)
    (hq : PlaneContinuous q) {M : X → RealGL3} (hM : Continuous M) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun x => functional (realCoefficientComponent n trivialCharacter (M x)
      (pointCanonical N (p x) (q x) h))) := by
  let basis := homogeneousBasis n
  simp_rw [pointCanonical_expand, map_sum, map_smul, smul_eq_mul]
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · exact (continuous h ((binaryBasis n).coord j)).comp hp.2
  · have expand (x : X) :
        functional (realCoefficientComponent n trivialCharacter (M x)
          ((realUpperRadicalRep n).ρ (p x).left
            (realUpperBinaryValue n (realPlaneRadicalAction (p x).right (q x).left)
              (binaryBasis n j)))) =
        ∑ i, basis.coord i (realUpperBinaryValue n
            (realPlaneRadicalAction (p x).right (q x).left) (binaryBasis n j)) *
          functional (realCoefficientComponent n trivialCharacter
            (M x * realPlaneMatrix (SemidirectProduct.inl (p x).left)) (basis i)) := by
      conv_lhs => rw [← basis.sum_repr (realUpperBinaryValue n _ (binaryBasis n j))]
      simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, map_mul,
        Module.End.mul_apply, realPlaneMatrix_inl]
      rfl
    simp_rw [expand]
    apply continuous_finsetSum
    intro i _
    apply Continuous.mul
    · exact realUpperBinaryValue_functional_continuous (continuous_radicalAction hp.2 hq.1) _ _
    · exact realCoefficientComponent_functional_continuous _
        (hM.mul (planeContinuous_inlRadical hp.1).matrix) _ _

/-- The homogeneous form of `θκ` through the canonical cochain of `δκ`. -/
theorem planeHomogeneousCanonical_degenerate_eq
    (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (P Q : RealPlaneGroup) :
    planeHomogeneousCanonical (fun _ => κ) ![P, P, Q] =
      pointCanonical (binaryCoboundary κ) P (P⁻¹ * Q) + pointCanonical (fun _ => κ) 1 Q -
        pointCanonical (fun _ => κ) 1 P := by
  rw [planeHomogeneousCanonical_degenerate, pointCanonical_binaryCoboundary, mul_inv_cancel_left,
    pointCanonical_const_one, pointCanonical_const_one]
  abel

/-- **Continuity of the degenerate transferred integrand in the good-line coordinate.** -/
theorem lineTransferIntegrand_degenerate_continuous
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (binaryAmbientRepresentation n A κ h)))
    (y z : LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun u => functional (lineTransferIntegrand (fun _ => κ) ![y, y, z] u h)) := by
  have vertex (q : LineGroup) : PlaneContinuous (fun u =>
      gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix q)) :=
    planeContinuous_gsPlaneVertex _ (fun u => goodLineForm_lineMatrix u q)
  have inverse : Continuous (fun u => (standardGoodLineRealArgument u)⁻¹) :=
    continuous_standardGoodLineRealArgument.inv
  have coboundary (h' : BinaryAdelicGL)
      (test : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
      Continuous (fun A => test (binaryCoboundary κ A h')) := by
    simp only [binaryCoboundary_apply, map_sub]
    exact (continuous h' test).sub continuous_const
  have constant (h' : BinaryAdelicGL) (test : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
      Continuous (fun _ : BinaryRealGL => test (κ h')) := continuous_const
  have vertices (u : ℝ × ℝ) :
      (fun i => gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (![y, y, z] i))) =
        ![gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix y),
          gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix y),
          gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix z)] := by
    funext i
    fin_cases i <;> rfl
  unfold lineTransferIntegrand
  simp_rw [vertices, planeHomogeneousCanonical_degenerate_eq]
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub]
  exact ((pointCanonical_moved_continuous_of coboundary (vertex y) ((vertex y).inv.mul (vertex z))
    inverse h functional).add (pointCanonical_moved_continuous_of constant
      (planeContinuous_const 1) (vertex z) inverse h functional)).sub
    (pointCanonical_moved_continuous_of constant (planeContinuous_const 1) (vertex y) inverse h
      functional)

/-! ### Integrability -/

/-- **Absolute integrability of the degenerate transferred integrands** (`n ≥ 5`). -/
theorem lineTransferIntegrand_degenerate_integrable (large : 5 ≤ n)
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ h, ‖functional (κ h)‖ ≤ C)
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (binaryAmbientRepresentation n A κ h)))
    (y z : LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => functional (lineTransferIntegrand (fun _ => κ) ![y, y, z] u h))
      ((volume : Measure ℝ).prod volume) := by
  have compactBound : ∀ (K : Set BinaryRealGL), IsCompact K →
      ∀ test : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
        ∃ C : ℝ, ∀ A ∈ K, ∀ h', ‖test ((fun _ => κ) A h')‖ ≤ C := fun _ _ test => by
    obtain ⟨C, hC⟩ := bounded test
    exact ⟨C, fun _ _ h' => hC h'⟩
  obtain ⟨C, hC0, hC⟩ := lineTransferIntegrand_bound_of compactBound ![y, y, z] functional
  have dominating :
      Integrable (fun u => C * kernelBase (lineInput y u) ^ (-(((n : ℝ) + 3) / 4)))
      ((volume : Measure ℝ).prod volume) :=
    ((lineInput_measurePreserving y).integrable_comp_of_integrable
      (kernelBase_decay_integrable large)).const_mul _
  refine dominating.mono'
    (lineTransferIntegrand_degenerate_continuous continuous y z h functional).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  refine (hC u h).trans (le_of_eq ?_)
  change (cornerScale (gsVertex (standardGoodLineRealArgument u * lineMatrix y)) : ℝ) ^
    (((n : ℝ) + 3) / 2) * C = _
  rw [cornerScale_gsVertex (goodLineForm_lineMatrix u y), gsVertex_lineMatrix_corner,
    ← abs_of_pos (inv_pos.mpr (gsRadius_pos _)), gsRadius_inv_rpow, mul_comm]
  congr 2
  ring

/-- **The transfer of the canonical cochain of a binary coboundary is the coboundary of the
transfer of `θκ`** (`n ≥ 5`, `κ` bounded with continuous translates). -/
theorem lineTransferCochain_binaryCoboundary_of_bounded (large : 5 ≤ n)
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ h, ‖functional (κ h)‖ ≤ C)
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (binaryAmbientRepresentation n A κ h)))
    (a b : LineGroup) :
    lineTransferCochain (binaryCoboundary κ) a b =
      a • bridgeTransfer κ b - bridgeTransfer κ (a * b) + bridgeTransfer κ a :=
  lineTransferCochain_binaryCoboundary κ
    (lineTransferIntegrand_degenerate_integrable large bounded continuous) a b

/-- **Absolute integrability of the transferred integrand of a binary coboundary** (`n ≥ 5`). -/
theorem lineTransferIntegrand_binaryCoboundary_integrable (large : 5 ≤ n)
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ h, ‖functional (κ h)‖ ≤ C)
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (binaryAmbientRepresentation n A κ h)))
    (x : Fin 3 → LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => functional (lineTransferIntegrand (binaryCoboundary κ) x u h))
      ((volume : Measure ℝ).prod volume) := by
  have integrable := lineTransferIntegrand_degenerate_integrable large bounded continuous
  simp only [lineTransferIntegrand_binaryCoboundary, map_add, map_sub]
  exact ((integrable _ _ h functional).sub (integrable _ _ h functional)).add
    (integrable _ _ h functional)

end TernaryPeriodPolynomials.AnalyticClasses
