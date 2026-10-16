module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineRelativePosition
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DerivativeEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Symmetric.ProjectionPlane

@[expose] public section


/-!
# The real good-line transfer at orthogonal Levi elements

An orthogonal matrix of the plane parabolic with positive corner is block diagonal
`diag(r, 1)` with `r ∈ O(2)`. Consequently, for an orthogonal Levi element `k` of the real
good-line stabilizer, the relative vertex of `k` is the Levi point `(0, r)` and the relative
position of `a k` with respect to `a` is again a Levi point. Hence the transferred canonical
integrand vanishes on every simplex `(1, k, k c)` (because `N` vanishes on `O(2)`) and on every
simplex `(1, a, a k)` (because `μ(0) = 0`), and the derivative edge vanishes at `k`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- Orthogonal real `3 × 3` matrices. -/
def IsOrthogonal3 (y : RealGL3) : Prop := y.val.transpose * y.val = 1

theorem IsOrthogonal3.mul {y z : RealGL3} (hy : IsOrthogonal3 y) (hz : IsOrthogonal3 z) :
    IsOrthogonal3 (y * z) := by
  unfold IsOrthogonal3 at *
  rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ y.val,
    hy, Matrix.one_mul, hz]

theorem IsOrthogonal3.inv {y : RealGL3} (hy : IsOrthogonal3 y) : IsOrthogonal3 y⁻¹ := by
  unfold IsOrthogonal3 at *
  have right : y.val * y.val.transpose = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) ℝ rfl).mp hy
  have inverse : (y⁻¹ : RealGL3).val = y.val.transpose := by
    have := congrArg (fun M => (y⁻¹ : RealGL3).val * M) right
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_one] at this
    exact this.symm
  rw [inverse, Matrix.transpose_transpose, right]

theorem isOrthogonal3_gsOrth (u : ℝ × ℝ) : IsOrthogonal3 (gsOrth u) := gsOrth_orthogonal u

theorem isOrthogonal3_planeLevi {k : BinaryRealGL} (hk : k.val.transpose * k.val = 1) :
    IsOrthogonal3 (planeLevi k 1) := by
  unfold IsOrthogonal3
  have entry (i j : Fin 2) : (k.val.transpose * k.val) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j :=
    by rw [hk]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at entry
  have e00 := entry 0 0
  have e01 := entry 0 1
  have e10 := entry 1 0
  have e11 := entry 1 1
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero,
    not_false_eq_true] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith

/-- An orthogonal plane-parabolic matrix with positive corner is `diag(r, 1)`. -/
theorem orthogonal_parabolic_structure {p : RealGL3} (orthogonal : IsOrthogonal3 p)
    (parabolic : p ∈ planeParabolic ℝ) (positive : 0 < p.val 2 2) :
    p.val 2 2 = 1 ∧ p.val 0 2 = 0 ∧ p.val 1 2 = 0 := by
  have h20 : p.val 2 0 = 0 := parabolic.1
  have h21 : p.val 2 1 = 0 := parabolic.2
  have right : p.val * p.val.transpose = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) ℝ rfl).mp orthogonal
  have row2 := congrFun (congrFun right 2) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, h20, h21,
    Matrix.one_apply_eq] at row2
  have corner : p.val 2 2 = 1 := by nlinarith
  have column := congrFun (congrFun orthogonal 2) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, corner,
    Matrix.one_apply_eq] at column
  refine ⟨corner, by nlinarith [sq_nonneg (p.val 0 2), sq_nonneg (p.val 1 2)],
    by nlinarith [sq_nonneg (p.val 0 2), sq_nonneg (p.val 1 2)]⟩

theorem planeNormalize_orthogonal {p : RealGL3} (orthogonal : IsOrthogonal3 p)
    (parabolic : p ∈ planeParabolic ℝ) (positive : 0 < p.val 2 2) :
    (planeNormalize p).left = 1 ∧
      (planeNormalize p).right • UpperHalfPlane.I = UpperHalfPlane.I := by
  obtain ⟨corner, first, second⟩ := orthogonal_parabolic_structure orthogonal parabolic positive
  constructor
  · apply Multiplicative.toAdd.injective
    funext i
    rw [planeNormalize_radical parabolic positive]
    fin_cases i <;> simp [first, second, corner]
  · apply UpperHalfPlane.ext
    rw [coe_smul_I_eq_positivePoint]
    have block : (planeNormalize p).right.val * (planeNormalize p).right.val.transpose = 1 := by
      have right : p.val * p.val.transpose = 1 :=
        (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) ℝ rfl).mp orthogonal
      ext i j
      have entry := congrFun (congrFun right i.castSucc) j.castSucc
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] at entry
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
        planeNormalize_levi_val parabolic positive, corner, div_one]
      fin_cases i <;> fin_cases j <;> simp_all
    rw [block]
    simp [positivePoint]

/-- Orthogonal elements of the real Levi. -/
def IsOrthogonalLevi (k : unimodularLevi) : Prop :=
  (k : BinaryRealGL).val.transpose * (k : BinaryRealGL).val = 1

theorem gsVertex_orthogonal_of {y : RealGL3} (hy : IsOrthogonal3 y) :
    IsOrthogonal3 (gsVertex y) :=
  hy.mul (isOrthogonal3_gsOrth _).inv

/-- The relative vertex of an orthogonal Levi element is a Levi point fixing `i`. -/
theorem relativeVertex_orthogonal (u : ℝ × ℝ) {k : unimodularLevi} (hk : IsOrthogonalLevi k) :
    (relativeVertex u (lineLeviElement k)).left = 1 ∧
      (relativeVertex u (lineLeviElement k)).right • UpperHalfPlane.I = UpperHalfPlane.I := by
  unfold relativeVertex gsPlaneVertex
  apply planeNormalize_orthogonal
  · rw [lineMatrix_lineLeviElement]
    exact gsVertex_orthogonal_of ((isOrthogonal3_gsOrth u).mul (isOrthogonal3_planeLevi hk))
  · exact gsVertex_orth_mem u _
  · exact gsVertex_orth_corner_pos u _

/-- Right multiplication by an orthogonal Levi element moves the relative vertex by a Levi point. -/
theorem relativeVertex_mul_orthogonal (u : ℝ × ℝ) (a : LineGroup) {k : unimodularLevi}
    (hk : IsOrthogonalLevi k) :
    ((relativeVertex u a)⁻¹ * relativeVertex u (a * lineLeviElement k)).left = 1 := by
  set y := gsOrth u * lineMatrix a
  set y' := gsOrth u * lineMatrix (a * lineLeviElement k)
  have hy' : y' = y * planeLevi (k : BinaryRealGL) 1 := by
    simp only [y', y, map_mul, lineMatrix_lineLeviElement, mul_assoc]
  set O := (gsVertex y)⁻¹ * gsVertex y'
  have vertex : gsVertex y' = gsVertex y * O := by rw [mul_inv_cancel_left]
  have memO : O ∈ planeParabolic ℝ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (gsVertex_orth_mem u a))
      (gsVertex_orth_mem u (a * lineLeviElement k))
  have orthO : IsOrthogonal3 O := by
    have : O = gsOrth (gsChart y) * planeLevi (k : BinaryRealGL) 1 *
        (gsOrth (gsChart y'))⁻¹ := by
      simp only [O, gsVertex, hy', _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact ((isOrthogonal3_gsOrth _).mul (isOrthogonal3_planeLevi hk)).mul
      (isOrthogonal3_gsOrth _).inv
  have cornerO : 0 < O.val 2 2 := by
    have whole := gsVertex_orth_corner_pos u (a * lineLeviElement k)
    rw [vertex, planeParabolic_mul_lastRow (gsVertex_orth_mem u a)] at whole
    exact pos_of_mul_pos_right whole (gsVertex_orth_corner_pos u a).le
  unfold relativeVertex gsPlaneVertex
  rw [vertex, planeNormalize_mul (gsVertex_orth_mem u a) memO (gsVertex_orth_corner_pos u a)
    cornerO, inv_mul_cancel_left]
  exact (planeNormalize_orthogonal orthO memO cornerO).1

theorem realUpperBinaryValue_one (P : Binary.HomogeneousPoly (n + 1)) :
    realUpperBinaryValue n 1 P = 0 := by
  unfold realUpperBinaryValue
  simp

/-- The transferred integrand vanishes on simplices `(1, k, c)` with `k` orthogonal. -/
theorem relativeIntegrand_orthogonal_first
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (vanish : ∀ A : BinaryRealGL, A • UpperHalfPlane.I = UpperHalfPlane.I → N A = 0)
    (u : ℝ × ℝ) {k : unimodularLevi} (hk : IsOrthogonalLevi k) (c : LineGroup)
    (h : BinaryAdelicGL) :
    relativeIntegrand N u (lineLeviElement k) c h = 0 := by
  unfold relativeIntegrand pointCanonical
  rw [vanish _ (relativeVertex_orthogonal u hk).2]
  simp

/-- The transferred integrand vanishes on simplices `(1, a, a k)` with `k` orthogonal. -/
theorem relativeIntegrand_orthogonal_second
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (a : LineGroup) {k : unimodularLevi} (hk : IsOrthogonalLevi k)
    (h : BinaryAdelicGL) :
    relativeIntegrand N u a (a * lineLeviElement k) h = 0 := by
  unfold relativeIntegrand pointCanonical
  rw [relativeVertex_mul_orthogonal u a hk, map_one, realUpperBinaryValue_one]
  simp

/-- The inhomogeneous real good-line transfer. -/
abbrev lineTransferCochain (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    LineGroup → LineGroup → LineValues n :=
  inhomogeneousOfHomogeneous (lineTransfer N)

theorem lineTransferCochain_apply
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (a b : LineGroup)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    lineTransferCochain N a b (h, functional) =
      ∫ u, functional (relativeIntegrand N u a (a * b) h) ∂((volume : Measure ℝ).prod volume) := by
  change ∫ u, functional (lineTransferIntegrand N ![1, a, a * b] u h) ∂_ = _
  simp only [lineTransferIntegrand_eq_relative]

theorem lineTransferCochain_orthogonal_left
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (vanish : ∀ A : BinaryRealGL, A • UpperHalfPlane.I = UpperHalfPlane.I → N A = 0)
    {k : unimodularLevi} (hk : IsOrthogonalLevi k) (b : LineGroup) :
    lineTransferCochain N (lineLeviElement k) b = 0 := by
  funext p
  rw [lineTransferCochain_apply]
  simp only [relativeIntegrand_orthogonal_first vanish _ hk, map_zero, integral_zero]
  rfl

theorem lineTransferCochain_orthogonal_right
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (a : LineGroup) {k : unimodularLevi} (hk : IsOrthogonalLevi k) :
    lineTransferCochain N a (lineLeviElement k) = 0 := by
  funext p
  rw [lineTransferCochain_apply]
  simp only [relativeIntegrand_orthogonal_second N _ a hk, map_zero, integral_zero]
  rfl

/-- **The derivative edge vanishes at orthogonal Levi elements.** -/
theorem derivativeEdge_orthogonal
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (vanish : ∀ A : BinaryRealGL, A • UpperHalfPlane.I = UpperHalfPlane.I → N A = 0)
    {k : unimodularLevi} (hk : IsOrthogonalLevi k) :
    derivativeEdge (lineTransferCochain N) k = 0 := by
  have edge (Y : Fin 2 → ℝ) : radicalEdge (lineTransferCochain N) k Y = 0 := by
    rw [radicalEdge_eq, lineTransferCochain_orthogonal_left vanish hk,
      lineTransferCochain_orthogonal_right N _ hk, sub_zero]
  funext h
  have component (i : Fin 2) : edgeComponent (lineTransferCochain N) k i = 0 := by
    funext p
    unfold edgeComponent radicalEdgeDerivative
    simp only [edge]
    change fderiv ℝ (fun _ : Fin 2 → ℝ => (0 : ℂ)) 0 (Pi.single i 1) = 0
    simp
  unfold derivativeEdge
  simp only [component]
  have zero : (fun i : Fin 2 => lineVector (0 : LineValues n) h) = 0 := by
    funext i
    unfold lineVector
    exact Finset.sum_eq_zero (fun j _ => zero_smul ℂ _)
  rw [zero, map_zero]
  rfl

end TernaryPeriodPolynomials.AnalyticClasses
