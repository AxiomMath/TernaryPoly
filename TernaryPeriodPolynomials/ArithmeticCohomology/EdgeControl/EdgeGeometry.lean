module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.TotalControl
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.EdgeIntegrability

@[expose] public section


/-!
# Geometry of the transported edges of the total primitive

For real vertices `x, y` whose good-line translates lie in the big cell, the real-plane points
`π_x(u), π_y(u)` of the Gram–Schmidt vertices of `g(u) x, g(u) y` depend continuously on `u`, and
the edge argument `q(u) = π_x(u)⁻¹ π_y(u)` stays in a fixed compact set: its plane matrix is
`t(u) κ_x(u) (x⁻¹ y) κ_y(u)⁻¹` with orthogonal `κ`'s and a corner ratio `t(u)` bounded above and
below, because the corner of a Gram–Schmidt vertex is the Euclidean length of the last row.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

section Units

variable {X : Type*} [TopologicalSpace X]

theorem continuous_matrix_inv {f : X → Matrix (Fin 2) (Fin 2) ℝ} (hf : Continuous f)
    (hdet : ∀ x, (f x).det ≠ 0) : Continuous (fun x => (f x)⁻¹) := by
  have equality : (fun x => (f x)⁻¹) = fun x => ((f x).det)⁻¹ • (f x).adjugate := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [equality]
  exact (hf.matrix_det.inv₀ hdet).smul hf.matrix_adjugate

/-- A family of invertible `2 × 2` matrices is continuous as soon as its entries are. -/
theorem continuous_units_of_val {f : X → BinaryRealGL}
    (hf : Continuous (fun x => (f x : Matrix (Fin 2) (Fin 2) ℝ))) : Continuous f := by
  apply Units.continuous_iff.mpr
  refine ⟨hf, ?_⟩
  have equality : (fun x => ((f x)⁻¹ : BinaryRealGL).val) = fun x => ((f x).val)⁻¹ := by
    funext x
    rw [Matrix.coe_units_inv]
  rw [equality]
  exact continuous_matrix_inv hf (fun x => (f x).det_ne_zero)

/-- **The real-plane point of a continuous family in the big cell is continuous.** -/
theorem planeContinuous_planeNormalize {h : X → RealGL3} (hh : Continuous h)
    (parabolic : ∀ x, h x ∈ planeParabolic ℝ) (positive : ∀ x, 0 < (h x).val 2 2) :
    PlaneContinuous (fun x => planeNormalize (h x)) := by
  have entry (i j : Fin 3) : Continuous (fun x => (h x).val i j) :=
    (Units.continuous_val.comp hh).matrix_elem i j
  have corner : Continuous (fun x => ((h x).val 2 2)⁻¹) :=
    (entry 2 2).inv₀ (fun x => (positive x).ne')
  have matrix (x : X) : (realPlaneMatrix (planeNormalize (h x))).val =
      ((h x).val 2 2)⁻¹ • (h x).val := by
    rw [realPlaneMatrix_planeNormalize (parabolic x) (positive x), Units.val_mul, scalar_val_three,
      cornerScale_val (positive x).ne', abs_of_pos (positive x)]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul]
  constructor
  · have equality (x : X) : (planeNormalize (h x)).left.toAdd =
        fun i => ((h x).val 2 2)⁻¹ * (h x).val i.castSucc 2 := by
      funext i
      rw [← realPlaneMatrix_radical_entry, matrix]
      rfl
    simp only [equality]
    exact continuous_pi (fun i => corner.mul (entry _ _))
  · apply continuous_units_of_val
    have equality (x : X) : ((planeNormalize (h x)).right : Matrix (Fin 2) (Fin 2) ℝ) =
        fun i j => ((h x).val 2 2)⁻¹ * (h x).val i.castSucc j.castSucc := by
      funext i j
      rw [← realPlaneMatrix_binary_entry, matrix]
      rfl
    simp only [equality]
    exact continuous_pi (fun i => continuous_pi (fun j => corner.mul (entry _ _)))

end Units

section Corner

/-- The squared Euclidean length of the last row. -/
def lastRowSq (y : RealGL3) : ℝ := ∑ j, (y.val 2 j) ^ 2

/-- The squared Frobenius norm. -/
def frobeniusSq (w : RealGL3) : ℝ := ∑ i, ∑ j, (w.val i j) ^ 2

/-- **The corner of a Gram–Schmidt vertex in the big cell is the length of the last row.** -/
theorem gsVertex_corner_sq (y : RealGL3) (parabolic : gsVertex y ∈ planeParabolic ℝ) :
    ((gsVertex y).val 2 2) ^ 2 = lastRowSq y := by
  have h20 : (gsVertex y).val 2 0 = 0 := parabolic.1
  have h21 : (gsVertex y).val 2 1 = 0 := parabolic.2
  have decomposition : y = gsVertex y * gsOrth (gsChart y) := by
    rw [gsVertex_eq_mul, inv_mul_cancel_right]
  have row (j : Fin 3) : y.val 2 j = (gsVertex y).val 2 2 * (gsOrth (gsChart y)).val 2 j := by
    conv_lhs => rw [decomposition]
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]
    ring
  have orthogonal := congrFun (congrFun (gsOrthMatrix_mul_transpose (gsChart y)) 2) 2
  rw [Matrix.mul_apply] at orthogonal
  simp only [Matrix.transpose_apply, Matrix.one_apply_eq] at orthogonal
  unfold lastRowSq
  simp only [row, mul_pow]
  rw [← Finset.mul_sum]
  have sum : ∑ j, ((gsOrth (gsChart y)).val 2 j) ^ 2 = 1 := by
    rw [← orthogonal]
    apply Finset.sum_congr rfl
    intro j _
    rw [sq]
    rfl
  rw [sum, mul_one]

/-- Cauchy–Schwarz for the last row of a product. -/
theorem lastRowSq_mul_le (y w : RealGL3) : lastRowSq (y * w) ≤ frobeniusSq w * lastRowSq y := by
  unfold lastRowSq frobeniusSq
  have column (j : Fin 3) : ((y * w).val 2 j) ^ 2 ≤ (∑ i, (y.val 2 i) ^ 2) * ∑ i, (w.val i j) ^
      2 := by
    rw [Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ j, ((y * w).val 2 j) ^ 2 ≤ ∑ j, (∑ i, (y.val 2 i) ^ 2) * ∑ i, (w.val i j) ^ 2 :=
        Finset.sum_le_sum (fun j _ => column j)
    _ = (∑ i, ∑ j, (w.val i j) ^ 2) * ∑ i, (y.val 2 i) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm, mul_comm]

theorem frobeniusSq_pos (w : RealGL3) : 0 < frobeniusSq w := by
  by_contra nonpositive
  have zero : ∀ i j, w.val i j = 0 := by
    intro i j
    have le : (w.val i j) ^ 2 ≤ frobeniusSq w := by
      unfold frobeniusSq
      refine (Finset.single_le_sum (f := fun j => (w.val i j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ j)).trans ?_
      exact Finset.single_le_sum (f := fun i => ∑ j, (w.val i j) ^ 2)
        (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm (le.trans (not_lt.mp
        nonpositive))
      (sq_nonneg _))
  have matrix : w.val = 0 := by
    ext i j
    exact zero i j
  have := w.det_ne_zero
  rw [matrix, Matrix.det_zero] at this
  exact this rfl

/-- **The corner ratio of two Gram–Schmidt vertices is bounded.** -/
theorem gsVertex_corner_ratio_le (y z : RealGL3) (py : gsVertex y ∈ planeParabolic ℝ)
    (pz : gsVertex z ∈ planeParabolic ℝ) (hy : 0 < (gsVertex y).val 2 2)
    (hz : 0 < (gsVertex z).val 2 2) :
    (gsVertex z).val 2 2 ≤ Real.sqrt (frobeniusSq (y⁻¹ * z)) * (gsVertex y).val 2 2 := by
  have bound := lastRowSq_mul_le y (y⁻¹ * z)
  rw [mul_inv_cancel_left, ← gsVertex_corner_sq z pz, ← gsVertex_corner_sq y py] at bound
  rw [← Real.sqrt_sq hz.le, ← Real.sqrt_sq hy.le, ← Real.sqrt_mul (frobeniusSq_pos _).le]
  exact Real.sqrt_le_sqrt bound

end Corner

section Shape

/-- The upper-left block of a `3 × 3` matrix. -/
def upperBlock (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => M i.castSucc j.castSucc

/-- The real-plane point of a matrix with last row `(0, 0, 1)`. -/
def matrixPlanePoint (M : Matrix (Fin 3) (Fin 3) ℝ) : RealPlaneGroup :=
  ⟨Multiplicative.ofAdd (fun i : Fin 2 => M i.castSucc 2), invertibleMatrix (upperBlock M)⟩

theorem matrixPlanePoint_realPlaneMatrix (element : RealPlaneGroup) :
    matrixPlanePoint (realPlaneMatrix element).val = element := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    exact realPlaneMatrix_radical_entry element i
  · change invertibleMatrix (upperBlock (realPlaneMatrix element).val) = element.right
    have block : upperBlock (realPlaneMatrix element).val = element.right.val := by
      funext i j
      exact realPlaneMatrix_binary_entry element i j
    rw [block, invertibleMatrix_coe]

theorem det_eq_upperBlock {M : Matrix (Fin 3) (Fin 3) ℝ} (h20 : M 2 0 = 0) (h21 : M 2 1 = 0)
    (h22 : M 2 2 = 1) : M.det = (upperBlock M).det := by
  simp only [Matrix.det_fin_three, Matrix.det_fin_two, upperBlock, h20, h21, h22]
  simp

/-- The compact set of plane matrices of bounded shape `t κ w κ'`. -/
def shapeSet (w : RealGL3) (a b : ℝ) : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  ((fun point : ℝ × RealGL3 × RealGL3 => point.1 • (point.2.1.val * w.val * point.2.2.val)) ''
      (Set.Icc a b ×ˢ (realOrthogonalSet ×ˢ realOrthogonalSet))) ∩
    {M | M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 2 2 = 1}

theorem shapeSet_isCompact (w : RealGL3) (a b : ℝ) : IsCompact (shapeSet w a b) := by
  apply IsCompact.inter_right
  · apply (isCompact_Icc.prod (realOrthogonalSet_isCompact.prod realOrthogonalSet_isCompact)).image
    have first : Continuous (fun point : ℝ × RealGL3 × RealGL3 => point.2.1.val) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_snd)
    have second : Continuous (fun point : ℝ × RealGL3 × RealGL3 => point.2.2.val) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_snd)
    exact continuous_fst.smul ((first.mul continuous_const).mul second)
  · have entry (i j : Fin 3) : Continuous (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) :=
      continuous_id.matrix_elem i j
    exact ((isClosed_eq (entry 2 0) continuous_const).inter
      ((isClosed_eq (entry 2 1) continuous_const).inter (isClosed_eq (entry 2 2) continuous_const)))

theorem shapeSet_upperBlock_det {w : RealGL3} {a b : ℝ} (ha : 0 < a)
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ shapeSet w a b) : (upperBlock M).det ≠ 0 := by
  obtain ⟨⟨⟨t, κ, κ'⟩, ⟨ht, -, -⟩, equality⟩, h20, h21, h22⟩ := hM
  rw [← det_eq_upperBlock h20 h21 h22, ← equality]
  simp only [Matrix.det_smul, Matrix.det_mul, Fintype.card_fin]
  have tpos : 0 < t := ha.trans_le ht.1
  exact mul_ne_zero (pow_ne_zero _ tpos.ne')
    (mul_ne_zero (mul_ne_zero κ.det_ne_zero w.det_ne_zero) κ'.det_ne_zero)

/-- **The plane point of a bounded-shape matrix depends continuously on it.** -/
theorem shapeSet_planeContinuous {w : RealGL3} {a b : ℝ} (ha : 0 < a) :
    PlaneContinuous (fun M : shapeSet w a b => matrixPlanePoint M.val) := by
  have entry (i j : Fin 3) : Continuous (fun M : shapeSet w a b => M.val i j) :=
    continuous_subtype_val.matrix_elem i j
  constructor
  · exact continuous_pi (fun i => entry _ _)
  · apply continuous_units_of_val
    have equality : (fun M : shapeSet w a b =>
        ((matrixPlanePoint M.val).right : Matrix (Fin 2) (Fin 2) ℝ)) =
        fun M => upperBlock M.val := by
      funext M
      exact OrbitSmooth.invertibleMatrix_val _ (shapeSet_upperBlock_det ha M.property)
    rw [equality]
    exact continuous_pi (fun i => continuous_pi (fun j => entry _ _))

/-- **Uniform sup bound of a controlled one-cochain on bounded-shape arguments.** -/
theorem OneControlled.shape_bound {degree : ℕ} {cusp : CuspidalRepresentation}
    {cochain : RealPlaneGroup → cuspidalTensorValues cusp (HomogeneousPoly degree)}
    (controlled : OneControlled cusp cochain) (w : RealGL3) {a b : ℝ} (ha : 0 < a)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M ∈ shapeSet w a b, CuspSupNorm.cuspSupNorm
      (cuspidalTensorFunctional cusp functional (cochain (matrixPlanePoint M))) ≤ C := by
  have continuity := (controlled (shapeSet w a b) _ (shapeSet_planeContinuous ha)).continuous_one
    functional
  have compact : CompactSpace (shapeSet w a b) :=
    isCompact_iff_compactSpace.mp (shapeSet_isCompact w a b)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn continuity.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun M hM => ?_⟩
  have bound := hC ⟨M, hM⟩ (Set.mem_univ _)
  rw [Real.norm_of_nonneg (norm_nonneg _)] at bound
  exact bound.trans (le_max_left _ _)

end Shape

section EdgeArgument

theorem gsPlaneVertex_matrix {X : RealGL3} (form : GoodLineForm X) :
    realPlaneMatrix (gsPlaneVertex X) = GeneralLinearGroup.scalar (Fin 3) (cornerScale (gsVertex
        X)) *
      (X * (gsOrth (gsChart X))⁻¹) :=
  realPlaneMatrix_planeNormalize form.gsVertex_mem form.corner_pos

theorem scalar_mul_mul_commute (c : ℝˣ) (g h : RealGL3) :
    GeneralLinearGroup.scalar (Fin 3) c * (g * h) = g * (GeneralLinearGroup.scalar (Fin 3) c *
        h) := by
  rw [← mul_assoc, GeneralLinearGroup.scalar_commute, mul_assoc]

/-- **The plane matrix of the edge argument.** -/
theorem edgeArgument_matrix {X Y : RealGL3} (fx : GoodLineForm X) (fy : GoodLineForm Y) :
    realPlaneMatrix ((gsPlaneVertex X)⁻¹ * gsPlaneVertex Y) =
      GeneralLinearGroup.scalar (Fin 3) ((cornerScale (gsVertex X))⁻¹ * cornerScale (gsVertex Y)) *
        (gsOrth (gsChart X) * (X⁻¹ * Y) * (gsOrth (gsChart Y))⁻¹) := by
  rw [map_mul, map_inv, gsPlaneVertex_matrix fx, gsPlaneVertex_matrix fy]
  set a := GeneralLinearGroup.scalar (Fin 3) (cornerScale (gsVertex X))
  set b := GeneralLinearGroup.scalar (Fin 3) (cornerScale (gsVertex Y))
  set κ := gsOrth (gsChart X)
  set κ' := gsOrth (gsChart Y)
  have scalar : GeneralLinearGroup.scalar (Fin 3) ((cornerScale (gsVertex X))⁻¹ *
      cornerScale (gsVertex Y)) = a⁻¹ * b := by
    rw [map_mul, map_inv]
  rw [scalar]
  have commute : (X * κ⁻¹)⁻¹ * (a⁻¹ * b) = (a⁻¹ * b) * (X * κ⁻¹)⁻¹ := by
    rw [← scalar]
    exact (GeneralLinearGroup.scalar_commute _ _).symm
  calc (a * (X * κ⁻¹))⁻¹ * (b * (Y * κ'⁻¹)) = (X * κ⁻¹)⁻¹ * (a⁻¹ * b) * (Y * κ'⁻¹) := by
        rw [_root_.mul_inv_rev]
        group
    _ = (a⁻¹ * b) * ((X * κ⁻¹)⁻¹ * (Y * κ'⁻¹)) := by
        rw [commute, mul_assoc]
    _ = (a⁻¹ * b) * (κ * (X⁻¹ * Y) * κ'⁻¹) := by
        congr 1
        group

theorem cornerScale_gsVertex {X : RealGL3} (form : GoodLineForm X) :
    (cornerScale (gsVertex X) : ℝ) = ((gsVertex X).val 2 2)⁻¹ := by
  rw [cornerScale_val form.corner_pos.ne', abs_of_pos form.corner_pos]

/-- **The edge argument has bounded shape.** -/
theorem edgeArgument_mem (x y : RealGL3) (u : ℝ × ℝ)
    (fx : GoodLineForm (standardGoodLineRealArgument u * x))
    (fy : GoodLineForm (standardGoodLineRealArgument u * y)) :
    (realPlaneMatrix ((gsPlaneVertex (standardGoodLineRealArgument u * x))⁻¹ *
        gsPlaneVertex (standardGoodLineRealArgument u * y))).val ∈
      shapeSet (x⁻¹ * y) (Real.sqrt (frobeniusSq (x⁻¹ * y)))⁻¹
        (Real.sqrt (frobeniusSq (y⁻¹ * x))) := by
  set X := standardGoodLineRealArgument u * x with hX
  set Y := standardGoodLineRealArgument u * y with hY
  have quotientXY : X⁻¹ * Y = x⁻¹ * y := by
    rw [hX, hY, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have quotientYX : Y⁻¹ * X = y⁻¹ * x := by
    rw [hX, hY, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have cx := fx.corner_pos
  have cy := fy.corner_pos
  set t : ℝ := (gsVertex X).val 2 2 / (gsVertex Y).val 2 2 with ht
  have lower : (Real.sqrt (frobeniusSq (x⁻¹ * y)))⁻¹ ≤ t := by
    have ratio := gsVertex_corner_ratio_le X Y fx.gsVertex_mem fy.gsVertex_mem cx cy
    rw [quotientXY] at ratio
    rw [ht, le_div_iff₀ cy, inv_mul_le_iff₀ (Real.sqrt_pos.mpr (frobeniusSq_pos _))]
    exact ratio
  have upper : t ≤ Real.sqrt (frobeniusSq (y⁻¹ * x)) := by
    have ratio := gsVertex_corner_ratio_le Y X fy.gsVertex_mem fx.gsVertex_mem cy cx
    rw [quotientYX] at ratio
    rw [ht, div_le_iff₀ cy]
    exact ratio
  refine ⟨⟨(t, gsOrth (gsChart X), (gsOrth (gsChart Y))⁻¹),
    ⟨⟨lower, upper⟩, gsOrth_mem _, gsOrth_inv_mem _⟩, ?_⟩, ?_⟩
  · show t • ((gsOrth (gsChart X)).val * (x⁻¹ * y).val * ((gsOrth (gsChart Y))⁻¹).val) = _
    rw [edgeArgument_matrix fx fy, quotientXY]
    simp only [Units.val_mul]
    rw [scalar_val_three, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    congr 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, cornerScale_gsVertex fx, cornerScale_gsVertex fy,
      inv_inv, ht, div_eq_mul_inv]
  · refine ⟨?_, ?_, ?_⟩ <;> rw [realPlaneMatrix_last_row] <;> simp

end EdgeArgument

end TernaryPeriodPolynomials.EdgeControl
