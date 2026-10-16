module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.PrismIntegrability
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CoefficientContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.EdgeIntegrable

@[expose] public section


/-!
# Integrability of the real good-line transfer

For a pointwise binary cocycle `N` whose scalar tests are continuous in the matrix and bounded on
compact sets uniformly in the adelic argument, every transferred integrand of the canonical cochain
at a simplex of the real good-line stabilizer is absolutely integrable over `u ∈ ℝ²`: after the
Gram–Schmidt normalization, the integrand at a simplex with first vertex `1` is
`s(u)^{(n+3)/2} ρ(κ_u⁻¹) Canon(q₁, q₁⁻¹ q₂)(h A₀)` with relative positions `q` in a compact set and
`s(u) = (1 + |u|²)^{-1/2}`; the general case follows by equivariance.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl
open TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ}

/-- **Pointwise binary cocycles** with continuous scalar tests, bounded on compact sets. -/
structure BinaryPointCocycle (n : ℕ) where
  /-- The values: functions on `GL₂(𝔸)` with values in `Sym^{n+1}`. -/
  value : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)
  cocycle : IsBinaryPointCocycle value
  continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
    Continuous (fun A => functional (value A h))
  bounded : ∀ (K : Set BinaryRealGL), IsCompact K →
    ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ A ∈ K, ∀ h, ‖functional (value A h)‖ ≤ C

/-! ### The canonical cochain on bounded-shape arguments -/

/-- A basis of the binary coefficients. -/
abbrev binaryBasis (n : ℕ) := binaryHomogeneousBasis (n + 1)

theorem pointCanonical_expand
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (p q : RealPlaneGroup) (h : BinaryAdelicGL) :
    pointCanonical N p q h = ∑ j, (binaryBasis n).coord j (N p.right h) •
      (realUpperRadicalRep n).ρ p.left
        (realUpperBinaryValue n (realPlaneRadicalAction p.right q.left) (binaryBasis n j)) := by
  unfold pointCanonical
  conv_lhs => rw [← (binaryBasis n).sum_repr (N p.right h)]
  simp only [map_sum, map_smul, Module.Basis.coord_apply]

/-- **Uniform bound of the canonical cochain on compact sets of plane matrices.** -/
theorem pointCanonical_shape_bound (N : BinaryPointCocycle n) {w₁ w₂ : RealGL3}
    {a₁ b₁ a₂ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M₁ ∈ shapeSet w₁ a₁ b₁, ∀ M₂ ∈ shapeSet w₂ a₂ b₂, ∀ h,
      ‖functional (pointCanonical N.value (matrixPlanePoint M₁) (matrixPlanePoint M₂) h)‖ ≤ C := by
  set K₁ := shapeSet w₁ a₁ b₁
  set K₂ := shapeSet w₂ a₂ b₂
  have compact₁ : CompactSpace K₁ := isCompact_iff_compactSpace.mp (shapeSet_isCompact _ _ _)
  have compact₂ : CompactSpace K₂ := isCompact_iff_compactSpace.mp (shapeSet_isCompact _ _ _)
  have plane₁ := shapeSet_planeContinuous (w := w₁) (b := b₁) ha₁
  have plane₂ := shapeSet_planeContinuous (w := w₂) (b := b₂) ha₂
  -- the binary coordinates of `N` on the compact image of the Levi parts
  have leviCompact : IsCompact (Set.range fun M : K₁ => (matrixPlanePoint M.val).right) :=
    isCompact_range plane₁.2
  have coordinate (j : _) := N.bounded _ leviCompact ((binaryBasis n).coord j)
  choose C hC using coordinate
  -- the coefficient operators are continuous on the compact product
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

/-! ### Continuity in the good-line coordinate -/

/-- Scalar tests of coefficient-moved canonical values along continuous paths are continuous. -/
theorem pointCanonical_moved_continuous (N : BinaryPointCocycle n) {X : Type}
    [TopologicalSpace X] {p q : X → RealPlaneGroup} (hp : PlaneContinuous p)
    (hq : PlaneContinuous q) {M : X → RealGL3} (hM : Continuous M) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun x => functional (realCoefficientComponent n trivialCharacter (M x)
      (pointCanonical N.value (p x) (q x) h))) := by
  let basis := homogeneousBasis n
  simp_rw [pointCanonical_expand, map_sum, map_smul, smul_eq_mul]
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · exact (N.continuous h ((binaryBasis n).coord j)).comp hp.2
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

/-- The homogeneous canonical value as an alternating sum of inhomogeneous values. -/
theorem planeHomogeneousCanonical_eq_sum (N : BinaryPointCocycle n)
    (Q : Fin 3 → RealPlaneGroup) :
    planeHomogeneousCanonical N.value Q =
      pointCanonical N.value (Q 1) ((Q 1)⁻¹ * Q 2) -
        pointCanonical N.value (Q 0) ((Q 0)⁻¹ * Q 2) +
        pointCanonical N.value (Q 0) ((Q 0)⁻¹ * Q 1) := by
  have law := pointCanonical_cocycle N.cocycle (Q 0) ((Q 0)⁻¹ * Q 1) ((Q 1)⁻¹ * Q 2)
  have first : Q 0 * ((Q 0)⁻¹ * Q 1) = Q 1 := by group
  have second : (Q 0)⁻¹ * Q 1 * ((Q 1)⁻¹ * Q 2) = (Q 0)⁻¹ * Q 2 := by group
  rw [first, second] at law
  unfold planeHomogeneousCanonical
  linear_combination (norm := abel) law

/-- **Continuity of the transferred integrand in the good-line coordinate.** -/
theorem lineTransferIntegrand_continuous (N : BinaryPointCocycle n) (x : Fin 3 → LineGroup)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun u => functional (lineTransferIntegrand N.value x u h)) := by
  have vertex (i : Fin 3) : PlaneContinuous (fun u =>
      gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x i))) :=
    planeContinuous_gsPlaneVertex _ (fun u => goodLineForm_lineMatrix u (x i))
  have inverse : Continuous (fun u => (standardGoodLineRealArgument u)⁻¹) :=
    continuous_standardGoodLineRealArgument.inv
  unfold lineTransferIntegrand
  simp_rw [planeHomogeneousCanonical_eq_sum N, Pi.add_apply, Pi.sub_apply, map_add, map_sub]
  exact (((pointCanonical_moved_continuous N (vertex 1) ((vertex 1).inv.mul (vertex 2)) inverse h
    functional).sub (pointCanonical_moved_continuous N (vertex 0) ((vertex 0).inv.mul (vertex 2))
      inverse h functional)).add (pointCanonical_moved_continuous N (vertex 0)
        ((vertex 0).inv.mul (vertex 1)) inverse h functional))

/-! ### The uniform bound -/

/-- The transferred integrand after the Gram–Schmidt normalization of the first vertex. -/
theorem lineTransferIntegrand_apply
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (x : Fin 3 → LineGroup) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    lineTransferIntegrand N x u h =
      (normPower (GeneralLinearGroup.det (atInfinity
          (gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 0))).right))
          (((n : ℂ) + 3) / 2) *
        (((cornerScale (gsVertex (standardGoodLineRealArgument u * lineMatrix (x 0))) : ℝ) :
          ℂ)⁻¹ ^ (n + 3))) •
      realCoefficientComponent n trivialCharacter
        (lineMatrix (x 0) *
          (gsOrth (gsChart (standardGoodLineRealArgument u * lineMatrix (x 0))))⁻¹)
        (pointCanonical N
          ((gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 0)))⁻¹ *
            gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 1)))
          ((gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 1)))⁻¹ *
            gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 2)))
          (h * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u *
            lineMatrix (x 0))).right)) := by
  have matrix : (standardGoodLineRealArgument u)⁻¹ *
      realPlaneMatrix (gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x 0))) =
      GeneralLinearGroup.scalar (Fin 3)
          (cornerScale (gsVertex (standardGoodLineRealArgument u * lineMatrix (x 0)))) *
        (lineMatrix (x 0) *
          (gsOrth (gsChart (standardGoodLineRealArgument u * lineMatrix (x 0))))⁻¹) := by
    rw [gsPlaneVertex_matrix (goodLineForm_lineMatrix u (x 0)), ← mul_assoc,
      ← GeneralLinearGroup.scalar_commute, mul_assoc, mul_assoc (standardGoodLineRealArgument u),
      inv_mul_cancel_left]
  unfold lineTransferIntegrand planeHomogeneousCanonical
  rw [planeAmbientRepresentation_apply, realPlaneCuspidalTwist_apply, realPlaneBinaryInput_apply,
    map_smul, ← Module.End.mul_apply, ← map_mul, matrix, map_mul, Module.End.mul_apply,
    realCoefficientComponent_scalar, smul_smul]

/-- **Uniform bound of the transferred integrand.** -/
theorem lineTransferIntegrand_bound (N : BinaryPointCocycle n) (x : Fin 3 → LineGroup)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (h : BinaryAdelicGL),
      ‖functional (lineTransferIntegrand N.value x u h)‖ ≤
        (cornerScale (gsVertex (standardGoodLineRealArgument u * lineMatrix (x 0))) : ℝ) ^
          (((n : ℝ) + 3) / 2) * C := by
  obtain ⟨B, hB0, hB⟩ := functional_coefficient_bound (n := n) (lineMatrix (x 0)) functional
  set w₁ := (lineMatrix (x 0))⁻¹ * lineMatrix (x 1)
  set w₂ := (lineMatrix (x 1))⁻¹ * lineMatrix (x 2)
  have positive (w : RealGL3) : 0 < (Real.sqrt (frobeniusSq w))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (frobeniusSq_pos _))
  have bounds (m : Fin 3 →₀ ℕ) := pointCanonical_shape_bound N (w₁ := w₁)
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
  set Y := pointCanonical N.value ((gsPlaneVertex X)⁻¹ *
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

/-- The corner of the Gram–Schmidt vertex of a moved stabilizer element. -/
theorem gsVertex_lineMatrix_corner (u : ℝ × ℝ) (q : LineGroup) :
    (gsVertex (standardGoodLineRealArgument u * lineMatrix q)).val 2 2 =
      gsRadius (lineInput q u) := by
  rw [standardGoodLineRealArgument_lineMatrix,
    gsVertex_plane_standard (planeLevi_mem _ _), planeLevi_mul_corner, gsUpper_corner]

/-- **Absolute integrability of every transferred integrand** (`n ≥ 5`). -/
theorem lineTransferIntegrand_integrable (large : 5 ≤ n) (N : BinaryPointCocycle n)
    (x : Fin 3 → LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => functional (lineTransferIntegrand N.value x u h))
      ((volume : Measure ℝ).prod volume) := by
  obtain ⟨C, hC0, hC⟩ := lineTransferIntegrand_bound N x functional
  have dominating :
      Integrable (fun u => C * kernelBase (lineInput (x 0) u) ^ (-(((n : ℝ) + 3) / 4)))
      ((volume : Measure ℝ).prod volume) :=
    ((lineInput_measurePreserving (x 0)).integrable_comp_of_integrable
      (kernelBase_decay_integrable large)).const_mul _
  refine dominating.mono' (lineTransferIntegrand_continuous N x h functional).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  refine (hC u h).trans (le_of_eq ?_)
  rw [cornerScale_gsVertex (goodLineForm_lineMatrix u (x 0)), gsVertex_lineMatrix_corner,
    ← abs_of_pos (inv_pos.mpr (gsRadius_pos _)), gsRadius_inv_rpow, mul_comm]
  congr 2
  ring

end TernaryPeriodPolynomials.AnalyticClasses
