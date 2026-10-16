module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.PointwiseCanonical
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineVertices
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ProjectedTermDecomposition

@[expose] public section


/-!
# The real good-line transfer of a canonical cocycle

The real points of the good-line stabilizer form the group `LineGroup = ℝ² ⋊ SL₂^±(ℝ)`, embedded in
`GL₃(ℝ)` by `(Y, m) ↦ lowerPlaneUnipotent Y · planeLevi m 1` (the opposite of the plane parabolic,
with unimodular Levi). For a pointwise binary cocycle `N`, the homogeneous canonical cochain on
real-plane points, moved by the good-line argument `g(u)` and the Gram–Schmidt vertex map and
integrated over `u ∈ ℝ²`, is a `LineGroup`-equivariant homogeneous two-cochain `lineTransfer N`
with values in scalar tests `(h, λ) ↦ λ(⋯)(h)`.

Equivariance holds without any integrability (change of variables `u ↦ u ∗ q` is measure
preserving). Closedness holds on every configuration whose four faces are integrable.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-! ### The real good-line stabilizer -/

/-- Real binary matrices of determinant `±1`. -/
def unimodularLevi : Subgroup BinaryRealGL where
  carrier := {m | |m.val.det| = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.det_mul, abs_mul] at *
    rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have product : |(a⁻¹ : BinaryRealGL).val.det| * |a.val.det| = 1 := by
      rw [← abs_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.det_one, abs_one]
    rw [ha, mul_one] at product
    exact product

/-- The real radical of the good-line stabilizer, in row-vector coordinates. -/
abbrev LineRadical := Multiplicative (Fin 2 → ℝ)

/-- The Levi action `Y ↦ Y m⁻¹` on the line radical. -/
def lineRadicalAction : unimodularLevi →* MulAut LineRadical where
  toFun m :=
    { toFun := fun Y => Multiplicative.ofAdd (Matrix.vecMul Y.toAdd (m⁻¹ : BinaryRealGL).val)
      invFun := fun Y => Multiplicative.ofAdd (Matrix.vecMul Y.toAdd (m : BinaryRealGL).val)
      left_inv := fun Y => by
        change Multiplicative.ofAdd (Matrix.vecMul (Matrix.vecMul Y.toAdd _) _) = Y
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.vecMul_one]
        rfl
      right_inv := fun Y => by
        change Multiplicative.ofAdd (Matrix.vecMul (Matrix.vecMul Y.toAdd _) _) = Y
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.vecMul_one]
        rfl
      map_mul' := fun Y Z => by
        change Multiplicative.ofAdd (Matrix.vecMul (Y.toAdd + Z.toAdd) _) = _
        rw [Matrix.add_vecMul]
        rfl }
  map_one' := by
    ext Y i
    change (Matrix.vecMul Y.toAdd ((1 : unimodularLevi)⁻¹ : BinaryRealGL).val) i = Y.toAdd i
    simp
  map_mul' a b := by
    ext Y i
    change (Matrix.vecMul Y.toAdd ((a * b)⁻¹ : BinaryRealGL).val) i =
      (Matrix.vecMul (Matrix.vecMul Y.toAdd ((b⁻¹ : unimodularLevi) : BinaryRealGL).val)
        ((a⁻¹ : unimodularLevi) : BinaryRealGL).val) i
    rw [Matrix.vecMul_vecMul, ← Units.val_mul]
    simp only [_root_.mul_inv_rev, Subgroup.coe_inv]

theorem lineRadicalAction_apply (m : unimodularLevi) (Y : LineRadical) :
    (lineRadicalAction m Y).toAdd = Matrix.vecMul Y.toAdd (m⁻¹ : BinaryRealGL).val := rfl

/-- The real good-line stabilizer. -/
abbrev LineGroup := LineRadical ⋊[lineRadicalAction] unimodularLevi

/-- The lower plane unipotent of a line radical element. -/
def lineRadicalMatrix : LineRadical →* RealGL3 where
  toFun Y := lowerPlaneUnipotent (Y.toAdd 0) (Y.toAdd 1)
  map_one' := by
    apply Units.ext
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' Y Z := by
    apply Units.ext
    change (lowerPlaneUnipotent (Y.toAdd 0 + Z.toAdd 0) (Y.toAdd 1 + Z.toAdd 1)).val = _
    rw [Units.val_mul]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem planeLevi_mul_lineRadicalMatrix (m : unimodularLevi) (Y : LineRadical) :
    planeLevi (m : BinaryRealGL) 1 * lineRadicalMatrix Y =
      lineRadicalMatrix (lineRadicalAction m Y) * planeLevi (m : BinaryRealGL) 1 := by
  change _ = lowerPlaneUnipotent ((lineRadicalAction m Y).toAdd 0)
    ((lineRadicalAction m Y).toAdd 1) * planeLevi (m : BinaryRealGL) 1
  rw [lowerPlaneUnipotent_planeLevi_commute]
  have back : Matrix.vecMul (lineRadicalAction m Y).toAdd (m : BinaryRealGL).val = Y.toAdd := by
    rw [lineRadicalAction_apply, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.vecMul_one]
  have first := congrFun back 0
  have second := congrFun back 1
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at first second
  rw [first, second]
  rfl

/-- The embedding of the real good-line stabilizer in `GL₃(ℝ)`. -/
def lineMatrix : LineGroup →* RealGL3 :=
  SemidirectProduct.lift lineRadicalMatrix (planeLeviOneHom.comp unimodularLevi.subtype) (by
    intro m
    apply MonoidHom.ext
    intro Y
    change lineRadicalMatrix (lineRadicalAction m Y) =
      planeLevi (m : BinaryRealGL) 1 * lineRadicalMatrix Y * (planeLevi (m : BinaryRealGL) 1)⁻¹
    rw [planeLevi_mul_lineRadicalMatrix, mul_assoc, mul_inv_cancel, mul_one])

theorem lineMatrix_apply (q : LineGroup) :
    lineMatrix q = lineRadicalMatrix q.left * planeLevi (q.right : BinaryRealGL) 1 := rfl

theorem pivotConjugate_one : pivotConjugate 1 = 1 := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [pivotConjugate, binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem binaryPivotSwap_mul_self : (binaryPivotSwap * binaryPivotSwap : BinaryRealGL) = 1 := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem pivotConjugate_mul (a b : BinaryRealGL) :
    pivotConjugate (a * b) = pivotConjugate a * pivotConjugate b := by
  unfold pivotConjugate
  calc binaryPivotSwap * (a * b) * binaryPivotSwap =
      binaryPivotSwap * a * (binaryPivotSwap * binaryPivotSwap) * b * binaryPivotSwap := by
        rw [binaryPivotSwap_mul_self, mul_one]; group
    _ = _ := by group

theorem abs_det_pivotConjugate (m : BinaryRealGL) :
    |(pivotConjugate m).val.det| = |m.val.det| := by
  unfold pivotConjugate
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, abs_mul, abs_mul]
  have swap : |(binaryPivotSwap : BinaryRealGL).val.det| = 1 := by
    simp [binaryPivotSwap, Matrix.det_fin_two]
  rw [swap]
  ring

/-- The action of the real good-line stabilizer on the good-line coordinate. -/
def lineInput (q : LineGroup) (u : ℝ × ℝ) : ℝ × ℝ :=
  realLeviInput (q.right : BinaryRealGL) (realRadicalShift (q.left.toAdd 0, q.left.toAdd 1) u)

/-- **The good-line argument intertwines the real stabilizer.** -/
theorem standardGoodLineRealArgument_lineMatrix (u : ℝ × ℝ) (q : LineGroup) :
    standardGoodLineRealArgument u * lineMatrix q =
      planeLevi (pivotConjugate (q.right : BinaryRealGL)) 1 *
        standardGoodLineRealArgument (lineInput q u) := by
  rw [lineMatrix_apply, ← mul_assoc]
  change standardGoodLineRealArgument u * lowerPlaneUnipotent (q.left.toAdd 0, q.left.toAdd 1).1
    (q.left.toAdd 0, q.left.toAdd 1).2 * _ = _
  rw [standardGoodLineRealArgument_lowerUnipotent, standardGoodLineRealArgument_realLevi]
  rfl

theorem lineInput_measurePreserving (q : LineGroup) :
    MeasurePreserving (lineInput q) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) :=
  (realLeviInput_measurePreserving q.right.property).comp
    (realRadicalShift_measurePreserving _)

/-- The good-line coordinate action as a measurable equivalence. -/
def lineInputEquiv (q : LineGroup) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.addRight ((q.left.toAdd 1, q.left.toAdd 0) : ℝ × ℝ)).trans
    (realLeviEquiv
      (q.right : BinaryRealGL)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem lineInputEquiv_apply (q : LineGroup) (u : ℝ × ℝ) :
    lineInputEquiv q u = lineInput q u := rfl

theorem integral_lineInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℝ × ℝ → E) (q : LineGroup) :
    (∫ u : ℝ × ℝ, function (lineInput q u) ∂((volume : Measure ℝ).prod volume)) =
      ∫ u : ℝ × ℝ, function u ∂((volume : Measure ℝ).prod volume) := by
  have := (lineInput_measurePreserving q).integral_comp (lineInputEquiv q).measurableEmbedding
    function
  simpa only [lineInputEquiv_apply] using this

theorem integrable_lineInput_iff {E : Type*} [NormedAddCommGroup E] (function : ℝ × ℝ → E)
    (q : LineGroup) :
    Integrable (fun u => function (lineInput q u)) ((volume : Measure ℝ).prod volume) ↔
      Integrable function ((volume : Measure ℝ).prod volume) := by
  have := (lineInput_measurePreserving q).integrable_comp_emb
    (lineInputEquiv q).measurableEmbedding (g := function)
  simpa only [Function.comp_def, lineInputEquiv_apply] using this

/-- Every translate of a real stabilizer element by the good-line argument has good-line form. -/
theorem goodLineForm_lineMatrix (u : ℝ × ℝ) (q : LineGroup) :
    GoodLineForm (standardGoodLineRealArgument u * lineMatrix q) :=
  ⟨pivotConjugate (q.right : BinaryRealGL), lineInput q u,
    by rw [abs_det_pivotConjugate]; exact q.right.property,
    standardGoodLineRealArgument_lineMatrix u q⟩

/-! ### Scalar tests and the stabilizer action -/

variable {n : ℕ}

/-- Scalar tests of pointwise values: functions of an adelic point and a coefficient functional. -/
def LineValues (n : ℕ) := BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ) → ℂ

instance : AddCommGroup (LineValues n) := inferInstanceAs (AddCommGroup (_ → ℂ))

/-- The action of the real good-line stabilizer on scalar tests. -/
def lineSmul (q : LineGroup) (F : LineValues n) : LineValues n :=
  fun p => F (p.1 * atInfinity (pivotConjugate (q.right : BinaryRealGL)),
    p.2 ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix q))

instance : DistribMulAction LineGroup (LineValues n) where
  smul := lineSmul
  one_smul F := by
    funext p
    change F (p.1 * atInfinity (pivotConjugate ((1 : LineGroup).right : BinaryRealGL)),
      p.2 ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix 1)) = F p
    simp only [SemidirectProduct.one_right, OneMemClass.coe_one, pivotConjugate_one, atInfinity_one,
      mul_one, map_one]
    exact congrArg F (Prod.ext rfl (LinearMap.comp_id p.2))
  mul_smul a b F := by
    funext p
    change F (p.1 * atInfinity (pivotConjugate ((a * b).right : BinaryRealGL)),
        p.2 ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix (a * b))) =
      F (p.1 * atInfinity (pivotConjugate (a.right : BinaryRealGL)) *
          atInfinity (pivotConjugate (b.right : BinaryRealGL)),
        (p.2 ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix a)) ∘ₗ
          realCoefficientComponent n trivialCharacter (lineMatrix b))
    rw [SemidirectProduct.mul_right, Subgroup.coe_mul, pivotConjugate_mul, atInfinity_mul,
      ← mul_assoc, map_mul, map_mul, LinearMap.comp_assoc]
    rfl
  smul_zero q := rfl
  smul_add q F G := rfl

theorem lineValues_smul_apply (q : LineGroup) (F : LineValues n)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (q • F) (h, functional) = F (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)),
      functional ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix q)) := rfl

/-! ### The transfer -/

/-- The homogeneous canonical cochain on real-plane points (pointwise values). -/
def planeHomogeneousCanonical
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (Q : Fin 3 → RealPlaneGroup) : BinaryAdelicGL → HomogeneousPoly n :=
  planeAmbientRepresentation n (Q 0) (pointCanonical N ((Q 0)⁻¹ * Q 1) ((Q 1)⁻¹ * Q 2))

theorem planeHomogeneousCanonical_smul
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (p : RealPlaneGroup) (Q : Fin 3 → RealPlaneGroup) :
    planeHomogeneousCanonical N (fun i => p * Q i) =
      planeAmbientRepresentation n p (planeHomogeneousCanonical N Q) := by
  unfold planeHomogeneousCanonical
  simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

/-- The transferred integrand of the canonical cochain at a real stabilizer simplex. -/
def lineTransferIntegrand
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (x : Fin 3 → LineGroup) (u : ℝ × ℝ) : BinaryAdelicGL → HomogeneousPoly n :=
  fun h => realCoefficientComponent n trivialCharacter (standardGoodLineRealArgument u)⁻¹
    (planeHomogeneousCanonical N
      (fun i => gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (x i))) h)

/-- **The real good-line transfer** of the canonical cochain. -/
def lineTransfer (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (x : Fin 3 → LineGroup) : LineValues n :=
  fun p => ∫ u : ℝ × ℝ, p.2 (lineTransferIntegrand N x u p.1)
    ∂((volume : Measure ℝ).prod volume)

theorem normPower_det_unimodular {m : BinaryRealGL} (unimodular : |m.val.det| = 1) (z : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity m)) z = 1 := by
  rw [binary_normalizingFactor_eq]
  have : Real.log m.val.det = 0 := by
    rw [← Real.log_abs, unimodular, Real.log_one]
  rw [this]
  simp

/-- The integrand transforms under the real stabilizer by the coordinate action. -/
theorem lineTransferIntegrand_smul
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (q : LineGroup) (x : Fin 3 → LineGroup) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    lineTransferIntegrand N (fun i => q * x i) u h =
      realCoefficientComponent n trivialCharacter (lineMatrix q)
        (lineTransferIntegrand N x (lineInput q u)
          (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)))) := by
  set m' := pivotConjugate (q.right : BinaryRealGL)
  set w := lineInput q u
  have vertices :
      (fun i => gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (q * x i))) =
      fun i => SemidirectProduct.inr m' *
        gsPlaneVertex (standardGoodLineRealArgument w * lineMatrix (x i)) := by
    funext i
    rw [map_mul, ← mul_assoc, standardGoodLineRealArgument_lineMatrix, mul_assoc,
      gsPlaneVertex_levi _ _ (goodLineForm_lineMatrix w (x i)).corner_pos]
  unfold lineTransferIntegrand
  rw [vertices, planeHomogeneousCanonical_smul, planeAmbientRepresentation_apply,
    realPlaneCuspidalTwist_apply]
  simp only [SemidirectProduct.right_inr, realPlaneMatrix_inr, realPlaneBinaryInput_apply]
  rw [normPower_det_unimodular (by rw [abs_det_pivotConjugate]; exact q.right.property),
    one_smul, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  have relation := standardGoodLineRealArgument_lineMatrix u q
  calc (standardGoodLineRealArgument u)⁻¹ * planeLevi m' 1 =
      (standardGoodLineRealArgument u)⁻¹ * (planeLevi m' 1 * standardGoodLineRealArgument w) *
        (standardGoodLineRealArgument w)⁻¹ := by group
    _ = lineMatrix q * (standardGoodLineRealArgument w)⁻¹ := by rw [← relation]; group

/-- **Equivariance of the real transfer.** -/
theorem lineTransfer_smul (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (q : LineGroup) (x : Fin 3 → LineGroup) :
    lineTransfer N (fun i => q * x i) = q • lineTransfer N x := by
  funext p
  obtain ⟨h, functional⟩ := p
  rw [lineValues_smul_apply]
  unfold lineTransfer
  simp only [lineTransferIntegrand_smul, LinearMap.comp_apply]
  exact integral_lineInput (fun w => functional (realCoefficientComponent n trivialCharacter
    (lineMatrix q) (lineTransferIntegrand N x w
      (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)))))) q

end TernaryPeriodPolynomials.AnalyticClasses
