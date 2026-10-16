module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineTransferBounds

@[expose] public section


/-!
# Relative positions of moved good-line vertices

With the Iwasawa factorization `g(u) = b(u) k(u)` of the good-line argument, the Gram–Schmidt plane
vertex of a moved stabilizer element factors as
`gsPlaneVertex (g(u) y) = gsPlaneVertex (g(u)) · gsPlaneVertex (k(u) y)`.
Hence the relative positions of the vertices of a moved simplex only depend on the orthogonal
factor `k(u)` (which ranges over a compact set): this is the bounded geometry behind every
regularity statement for the real good-line transfer. The canonical cochain at a simplex with first
vertex `1` reads `ρ_U(x₁) μ(x₂ - x₁) N(A₁)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem cornerScale_mul {p q : RealGL3} (hp : p ∈ planeParabolic ℝ) (positive : 0 < p.val 2 2)
    (positive' : 0 < q.val 2 2) :
    cornerScale (p * q) = cornerScale p * cornerScale q := by
  have corner : (p * q).val 2 2 = p.val 2 2 * q.val 2 2 := planeParabolic_mul_lastRow hp q 2
  apply Units.ext
  rw [Units.val_mul, cornerScale_val (by rw [corner]; positivity), cornerScale_val positive.ne',
    cornerScale_val positive'.ne', corner, abs_mul, mul_inv]

/-- **The plane point is multiplicative on the plane parabolic.** -/
theorem planeNormalize_mul {p q : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (hq : q ∈ planeParabolic ℝ) (positive : 0 < p.val 2 2) (positive' : 0 < q.val 2 2) :
    planeNormalize (p * q) = planeNormalize p * planeNormalize q := by
  have corner : 0 < (p * q).val 2 2 := by
    rw [planeParabolic_mul_lastRow hp q 2]
    positivity
  apply realPlaneMatrix_injective
  rw [map_mul, realPlaneMatrix_planeNormalize (Subgroup.mul_mem _ hp hq) corner,
    realPlaneMatrix_planeNormalize hp positive, realPlaneMatrix_planeNormalize hq positive',
    cornerScale_mul hp positive positive', map_mul]
  rw [mul_assoc, mul_assoc, ← mul_assoc p, ← GeneralLinearGroup.scalar_commute, mul_assoc]

theorem gsVertex_goodLine_mul (u : ℝ × ℝ) (y : RealGL3) :
    gsVertex (standardGoodLineRealArgument u * y) = gsUpper u * gsVertex (gsOrth u * y) := by
  rw [standardGoodLineRealArgument_eq_gsUpper_mul, mul_assoc,
    gsVertex_plane_mul (gsUpper_mem_planeParabolic u)]

theorem gsUpper_corner_pos (u : ℝ × ℝ) : 0 < (gsUpper u).val 2 2 := by
  rw [gsUpper_corner]
  exact gsRadius_pos u

/-- The Gram–Schmidt vertex of `k(u) · lineMatrix q` lies in the plane parabolic. -/
theorem gsVertex_orth_mem (u : ℝ × ℝ) (q : LineGroup) :
    gsVertex (gsOrth u * lineMatrix q) ∈ planeParabolic ℝ := by
  have whole := (goodLineForm_lineMatrix u q).gsVertex_mem
  rw [gsVertex_goodLine_mul] at whole
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (gsUpper_mem_planeParabolic u)) whole
  rwa [inv_mul_cancel_left] at this

theorem gsVertex_orth_corner_pos (u : ℝ × ℝ) (q : LineGroup) :
    0 < (gsVertex (gsOrth u * lineMatrix q)).val 2 2 := by
  have whole := (goodLineForm_lineMatrix u q).corner_pos
  rw [gsVertex_goodLine_mul, planeParabolic_mul_lastRow (gsUpper_mem_planeParabolic u)] at whole
  exact pos_of_mul_pos_right whole (gsUpper_corner_pos u).le

/-- The relative plane position of a moved stabilizer element. -/
def relativeVertex (u : ℝ × ℝ) (q : LineGroup) : RealPlaneGroup :=
  gsPlaneVertex (gsOrth u * lineMatrix q)

/-- **Factorization of moved plane vertices.** -/
theorem gsPlaneVertex_goodLine (u : ℝ × ℝ) (q : LineGroup) :
    gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix q) =
      gsPlaneVertex (standardGoodLineRealArgument u) * relativeVertex u q := by
  unfold gsPlaneVertex relativeVertex
  rw [gsVertex_goodLine_mul, gsVertex_standard,
    planeNormalize_mul (gsUpper_mem_planeParabolic u) (gsVertex_orth_mem u q)
      (gsUpper_corner_pos u) (gsVertex_orth_corner_pos u q)]
  rfl

theorem gsChart_gsOrth (u : ℝ × ℝ) : gsChart (gsOrth u) = u := by
  have radius := gsRadius_pos u
  simp only [gsChart, gsOrth_val, gsOrthMatrix]
  simp [radius.ne']

theorem relativeVertex_one (u : ℝ × ℝ) : relativeVertex u 1 = 1 := by
  unfold relativeVertex gsPlaneVertex
  rw [map_one, mul_one, gsVertex, gsChart_gsOrth, mul_inv_cancel]
  apply realPlaneMatrix_injective
  rw [realPlaneMatrix_planeNormalize (Subgroup.one_mem _) (by simp), map_one]
  have : cornerScale (1 : RealGL3) = 1 := by
    apply Units.ext
    rw [cornerScale_val (by simp)]
    simp
  rw [this, map_one, one_mul]

/-! ### The transferred integrand in relative form -/

/-- The scale of the transferred integrand at the good-line coordinate `u`. -/
def transferScale (n : ℕ) (u : ℝ × ℝ) : ℂ :=
  normPower (GeneralLinearGroup.det (atInfinity
      (gsPlaneVertex (standardGoodLineRealArgument u)).right)) (((n : ℂ) + 3) / 2) *
    (((cornerScale (gsVertex (standardGoodLineRealArgument u)) : ℝ) : ℂ)⁻¹ ^ (n + 3))

/-- **The transferred integrand at a simplex `(1, a, c)` in relative form.** -/
def relativeIntegrand (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (a c : LineGroup) (h : BinaryAdelicGL) : HomogeneousPoly n :=
  transferScale n u • realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
    (pointCanonical N (relativeVertex u a) ((relativeVertex u a)⁻¹ * relativeVertex u c)
      (h * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u)).right))

theorem lineTransferIntegrand_eq_relative
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (a c : LineGroup) (h : BinaryAdelicGL) :
    lineTransferIntegrand N ![1, a, c] u h = relativeIntegrand N u a c h := by
  rw [lineTransferIntegrand_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_one, mul_one]
  rw [gsPlaneVertex_goodLine u a, gsPlaneVertex_goodLine u c, gsChart_standard, one_mul]
  unfold relativeIntegrand transferScale
  rw [inv_mul_cancel_left, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem radicalAction_relative (p p' : RealPlaneGroup) :
    realPlaneRadicalAction p.right (p⁻¹ * p').left = p.left⁻¹ * p'.left := by
  rw [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.inv_right, map_mul]
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

/-- The canonical cochain at a simplex with first vertex `1`: `ρ_U(x) μ(x' - x) N(A)`. -/
theorem pointCanonical_relative
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (p p' : RealPlaneGroup) (h : BinaryAdelicGL) :
    pointCanonical N p (p⁻¹ * p') h = (realUpperRadicalRep n).ρ p.left
      (realUpperBinaryValue n (p.left⁻¹ * p'.left) (N p.right h)) := by
  unfold pointCanonical
  rw [radicalAction_relative]

end TernaryPeriodPolynomials.AnalyticClasses
