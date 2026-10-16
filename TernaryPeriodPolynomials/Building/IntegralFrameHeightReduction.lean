module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import TernaryPeriodPolynomials.Building.Good.AugmentedNormalForm
public import TernaryPeriodPolynomials.Building.Primitive.LineHeight
public import TernaryPeriodPolynomials.Building.AugmentedFrame.HeightArithmetic
public import Mathlib.Tactic.Ring

@[expose] public section


noncomputable section
namespace TernaryPoly.IntegralFrameHeightReduction
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open GoodIntegralNormalization GoodAugmentedNormalForm PrimitiveLineHeight

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

/-- The sign that makes an integer nonnegative; zero uses the positive sign. -/
def positiveSign (z : ℤ) : ℤ := if 0 ≤ z then 1 else -1

theorem positiveSign_mul_self (z : ℤ) : positiveSign z * positiveSign z = 1 := by
  unfold positiveSign
  split_ifs <;> norm_num

theorem positiveSign_mul (z : ℤ) : positiveSign z * z = |z| := by
  unfold positiveSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

@[simp] theorem positiveSign_zero : positiveSign 0 = 1 := by simp [positiveSign]

/-- Nonnegative sign normalization of a literal integral vector. -/
def normalized (F : IntegralVector →ₗ[ℤ] ℤ) (v : IntegralVector) : IntegralVector :=
  positiveSign (F v) • v

theorem normalized_value (F : IntegralVector →ₗ[ℤ] ℤ) (v : IntegralVector) :
    F (normalized F v) = |F v| := by
  simp only [normalized,map_smul,smul_eq_mul,positiveSign_mul]

theorem normalized_nonneg (F : IntegralVector →ₗ[ℤ] ℤ) (v : IntegralVector) :
    0 ≤ F (normalized F v) := by rw [normalized_value]; exact abs_nonneg _

theorem normalized_eq_self (F : IntegralVector →ₗ[ℤ] ℤ) (v : IntegralVector)
    (hv : 0 ≤ F v) : normalized F v = v := by simp [normalized,positiveSign,hv]

theorem normalized_eq_neg (F : IntegralVector →ₗ[ℤ] ℤ) (v : IntegralVector)
    (hv : F v < 0) : normalized F v = -v := by
  simp [normalized,positiveSign,not_le.mpr hv]

theorem normalized_primitive (F : IntegralVector →ₗ[ℤ] ℤ) {v : IntegralVector}
    (hv : Primitive v) : Primitive (normalized F v) := by
  by_cases h : 0 ≤ F v
  · rw [normalized_eq_self F v h]
    exact hv
  · rw [normalized_eq_neg F v (lt_of_not_ge h)]
    exact hv.neg

/-- Sign normalization does not change the actual rational line, including at zero height. -/
theorem normalized_span (F : IntegralVector →ₗ[ℤ] ℤ) (v : IntegralVector) :
    Submodule.span ℚ {rationalVector (normalized F v)} = Submodule.span ℚ {rationalVector v} := by
  by_cases h : 0 ≤ F v
  · rw [normalized_eq_self F v h]
  · rw [normalized_eq_neg F v (lt_of_not_ge h),PrimitiveLineHeight.span_neg]

/-- The signed simultaneous shear, with arbitrary quotient coefficients. -/
def shearMatrix (s t p q : ℤ) : Mat := !![1,-p,-q;0,s,0;0,0,t]

def shearInverse (s t p q : ℤ) : Mat := !![1,p*s,q*t;0,s,0;0,0,t]

theorem shearMatrix_mul_inverse (s t p q : ℤ) (hs : s*s=1) (ht : t*t=1) :
    shearMatrix s t p q * shearInverse s t p q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearMatrix,shearInverse,Matrix.mul_apply,Fin.sum_univ_three,hs,ht]

theorem shearInverse_mul_matrix (s t p q : ℤ) (hs : s*s=1) (ht : t*t=1) :
    shearInverse s t p q * shearMatrix s t p q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearMatrix,shearInverse,Matrix.mul_apply,Fin.sum_univ_three,hs,ht,mul_assoc]

/-- An actual integral matrix unit, not an assumed frame-preservation map. -/
def signedShear (s t p q : ℤ) (hs : s*s=1) (ht : t*t=1) : IntegralGL :=
  ⟨shearMatrix s t p q,shearInverse s t p q,
    shearMatrix_mul_inverse s t p q hs ht,shearInverse_mul_matrix s t p q hs ht⟩

theorem mul_signedShear_col_zero (g : IntegralGL) (s t p q : ℤ)
    (hs : s*s=1) (ht : t*t=1) : (g * signedShear s t p q hs ht).val.col 0 = g.val.col 0 := by
  ext i
  simp [signedShear,shearMatrix,Matrix.col,Matrix.mul_apply,Fin.sum_univ_three]

theorem mul_signedShear_col_one (g : IntegralGL) (s t p q : ℤ)
    (hs : s*s=1) (ht : t*t=1) :
    (g * signedShear s t p q hs ht).val.col 1 = s • g.val.col 1 - p • g.val.col 0 := by
  ext i
  simp [signedShear,shearMatrix,Matrix.col,Matrix.mul_apply,Fin.sum_univ_three]
  ring

theorem mul_signedShear_col_two (g : IntegralGL) (s t p q : ℤ)
    (hs : s*s=1) (ht : t*t=1) :
    (g * signedShear s t p q hs ht).val.col 2 = t • g.val.col 2 - q • g.val.col 0 := by
  ext i
  simp [signedShear,shearMatrix,Matrix.col,Matrix.mul_apply,Fin.sum_univ_three]
  ring

/-- The quotient after making a basis column nonnegative. -/
def columnQuotient (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (j : Fin 3) : ℤ :=
  F (normalized F (g.val.col j)) / F (g.val.col 0)

/-- Simultaneous remainder reduction about the first column of the actual integral basis. -/
def reducedBasis (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) : IntegralGL :=
  g * signedShear (positiveSign (F (g.val.col 1))) (positiveSign (F (g.val.col 2)))
    (columnQuotient F g 1) (columnQuotient F g 2)
    (positiveSign_mul_self _) (positiveSign_mul_self _)

theorem reducedBasis_col_zero (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) :
    (reducedBasis F g).val.col 0 = g.val.col 0 := mul_signedShear_col_zero _ _ _ _ _ _ _

/-- Exact simultaneous signed-column and quotient-subtraction formula. -/
theorem reducedBasis_col_succ (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (j : Fin 2) :
    (reducedBasis F g).val.col j.succ = normalized F (g.val.col j.succ) -
      columnQuotient F g j.succ • g.val.col 0 := by
  fin_cases j
  · exact mul_signedShear_col_one _ _ _ _ _ _ _
  · exact mul_signedShear_col_two _ _ _ _ _ _ _

theorem reducedBasis_col_remainder (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (j : Fin 2) :
    (reducedBasis F g).val.col j.succ =
      remainderVector F (g.val.col 0) (normalized F (g.val.col j.succ)) :=
  reducedBasis_col_succ F g j

/-- All columns of any actual integer matrix unit are primitive. -/
theorem column_primitive (g : IntegralGL) (j : Fin 3) : Primitive (g.val.col j) := by
  have h := primitive_mulVec g (integralTemplate_primitive j.castSucc)
  fin_cases j <;> simpa [integralTemplate] using h

theorem reducedBasis_column_primitive (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (j : Fin 3) :
    Primitive ((reducedBasis F g).val.col j) := column_primitive _ _

/-- The first three augmented lines are exactly the primitive rational column lines. -/
theorem columnLine_span (g : IntegralGL) (j : Fin 3) :
    (augmentedLine g j.castSucc).val = Submodule.span ℚ {rationalVector (g.val.col j)} := by
  rw [augmentedLine_castSucc_val,rationalRepresentation_basis]
  rfl

theorem columnLine_height (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (j : Fin 3) :
    height F (augmentedLine g j.castSucc) = (F (g.val.col j)).natAbs :=
  height_eq_natAbs F _ (column_primitive g j) (columnLine_span g j).symm

/-- The first actual rational column line remains fixed. -/
theorem reducedBasis_line_zero (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) :
    augmentedLine (reducedBasis F g) 0 = augmentedLine g 0 := by
  apply Subtype.ext
  change (augmentedLine (reducedBasis F g) (0 : Fin 3).castSucc).val =
    (augmentedLine g (0 : Fin 3).castSucc).val
  rw [columnLine_span,columnLine_span,reducedBasis_col_zero]

/-- Each reduced complementary coordinate is the Euclidean remainder of the absolute old coordinate. -/
theorem reducedBasis_column_value (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (j : Fin 2) :
    F ((reducedBasis F g).val.col j.succ) = |F (g.val.col j.succ)| % F (g.val.col 0) := by
  rw [reducedBasis_col_remainder,remainderVector_value,normalized_value]

/-- Positive first-column height forces both reduced complementary line heights below it. -/
theorem reducedBasis_height_lt (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (hN : 0 < F (g.val.col 0)) (j : Fin 2) :
    (height F (augmentedLine (reducedBasis F g) j.succ.castSucc) : ℤ) < F (g.val.col 0) := by
  rw [columnLine_height,reducedBasis_column_value,Int.natCast_natAbs]
  obtain ⟨h0,hlt⟩ := AugmentedHeightArithmetic.remainder_bounds
    (F (g.val.col 0)) |F (g.val.col j.succ)| hN
  rwa [abs_of_nonneg h0]

/-- A complementary column whose old line is already low is unchanged after sign normalization. -/
theorem reducedBasis_col_eq_normalized_of_low (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (j : Fin 2)
    (hL : (height F (augmentedLine g j.succ.castSucc) : ℤ) < F (g.val.col 0)) :
    (reducedBasis F g).val.col j.succ = normalized F (g.val.col j.succ) := by
  rw [reducedBasis_col_remainder]
  apply remainderVector_eq_self F _ _ (normalized_nonneg F _)
  rw [normalized_value]
  simpa only [columnLine_height,Int.natCast_natAbs] using hL

/-- Every complementary line already below the first-column height is fixed as an actual line. -/
theorem reducedBasis_line_eq_of_low (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (j : Fin 2)
    (hL : (height F (augmentedLine g j.succ.castSucc) : ℤ) < F (g.val.col 0)) :
    augmentedLine (reducedBasis F g) j.succ.castSucc = augmentedLine g j.succ.castSucc := by
  apply Subtype.ext
  rw [columnLine_span,columnLine_span,reducedBasis_col_eq_normalized_of_low F g j hL,
    normalized_span]

/-- At zero functional value even the literal basis column is fixed, with no sign choice ambiguity. -/
theorem reducedBasis_col_eq_of_zero (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (j : Fin 2)
    (hz : F (g.val.col j.succ) = 0) : (reducedBasis F g).val.col j.succ = g.val.col j.succ := by
  rw [reducedBasis_col_succ]
  have hn : normalized F (g.val.col j.succ) = g.val.col j.succ :=
    normalized_eq_self F _ (by rw [hz])
  have hq : columnQuotient F g j.succ = 0 := by simp [columnQuotient,hn,hz]
  rw [hn,hq,zero_smul,sub_zero]

/-- The simultaneously reduced first-three-line simplex is an actual integral ambient face. -/
theorem reducedBasis_triangle_ambient (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) :
    {augmentedLine (reducedBasis F g) 0,augmentedLine (reducedBasis F g) 1,
      augmentedLine (reducedBasis F g) 2} ∈ ambient := by
  classical
  apply subset_augmentedFrame_mem (reducedBasis F g) (by simp)
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩

end TernaryPoly.IntegralFrameHeightReduction
