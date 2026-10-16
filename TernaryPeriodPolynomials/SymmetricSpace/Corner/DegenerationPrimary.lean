module

public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationBasic
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerDegeneration
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates

/-- A polynomial matrix model that remains nonzero on the whole closed root quadrant. -/
def weightedFlag (x y z s t : ℝ) : Mat :=
  upper x y z*Matrix.diagonal ![1,s^2,s^2*t^2]*(upper x y z).transpose

theorem weightedFlag_explicit (x y z s t : ℝ) :
    weightedFlag x y z s t=!![1+x^2*s^2+z^2*s^2*t^2,x*s^2+z*y*s^2*t^2,z*s^2*t^2;
      x*s^2+y*z*s^2*t^2,s^2+y^2*s^2*t^2,y*s^2*t^2;z*s^2*t^2,y*s^2*t^2,s^2*t^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weightedFlag,upper,Matrix.mul_apply,Matrix.vecMul_diagonal,Fin.sum_univ_succ] <;> ring

def rawA (p : Corner) : Mat := weightedFlag (p.1 0) (p.1 1) (p.1 2) p.2.1.val p.2.2.val

def A (p : Corner) : Mat := SymmetricSpacePositive.normalize (rawA p)

theorem rawA_psd (p : Corner) : (rawA p).PosSemidef := by
  have hd : (Matrix.diagonal ![(1 : ℝ),p.2.1.val^2,p.2.1.val^2*p.2.2.val^2]).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i
    · norm_num
    · exact sq_nonneg _
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  simpa only [rawA,weightedFlag,Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (upper (p.1 0) (p.1 1) (p.1 2))

theorem rawA_zero_zero_ge_one (p : Corner) : 1≤rawA p 0 0 := by
  rw [rawA,weightedFlag_explicit]
  change 1≤1+(p.1 0)^2*p.2.1.val^2+(p.1 2)^2*p.2.1.val^2*p.2.2.val^2
  have h1 := mul_nonneg (sq_nonneg (p.1 0)) (sq_nonneg p.2.1.val)
  have h2 := mul_nonneg (mul_nonneg (sq_nonneg (p.1 2)) (sq_nonneg p.2.1.val))
    (sq_nonneg p.2.2.val)
  linarith

theorem rawA_ne_zero (p : Corner) : rawA p≠0 := by
  intro h
  have he := rawA_zero_zero_ge_one p
  rw [h] at he
  norm_num at he

theorem rawA_trace_pos (p : Corner) : 0<(rawA p).trace := psd_trace_pos (rawA_psd p) (rawA_ne_zero p)

theorem A_psd (p : Corner) : (A p).PosSemidef := normalize_psd (rawA_psd p) (rawA_ne_zero p)

@[simp] theorem A_trace (p : Corner) : (A p).trace=1 := normalize_trace (ne_of_gt (rawA_trace_pos p))

theorem A_ne_zero (p : Corner) : A p≠0 := normalize_ne_zero (ne_of_gt (rawA_trace_pos p))

theorem continuous_rawA : Continuous rawA := by
  unfold rawA weightedFlag upper
  fun_prop

theorem continuous_A : Continuous A :=
  (continuous_rawA.matrix_trace.inv₀ (fun p => ne_of_gt (rawA_trace_pos p))).smul continuous_rawA

def E00 : Mat := Matrix.diagonal ![1,0,0]

@[simp] theorem E00_trace : E00.trace=1 := by simp [E00,Matrix.trace,Fin.sum_univ_succ]

theorem rawA_t1_zero (p : Corner) (hs : p.2.1.val=0) : rawA p=E00 := by
  rw [rawA,weightedFlag_explicit,hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E00]

theorem A_t1_zero (p : Corner) (hs : p.2.1.val=0) : A p=E00 := by
  rw [A,rawA_t1_zero p hs]
  exact normalize_of_trace_one _ E00_trace

/-- On the positive quadrant the polynomial model is a positive scalar multiple of the actual
reverse LDL representative. -/
theorem weightedFlag_eq_scaled_flag (x y z s t : ℝ) (hs : s≠0) (ht : t≠0) :
    weightedFlag x y z s t=(s^2*t^2) • flagMatrix x y z (s^2*t^2)⁻¹ (t^2)⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weightedFlag,flagMatrix,upper,SymmetricSpaceFlagCoordinates.diagonal,Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.transpose_apply,
      Fin.sum_univ_succ,smul_eq_mul] <;> field_simp [hs,ht]

theorem A_positive_parameters (p : RootParameters) :
    A (positiveCornerHomeomorph p).val=(rootHomeomorph.symm p).val := by
  change SymmetricSpacePositive.normalize
    (weightedFlag (p.1 0) (p.1 1) (p.1 2) p.2.1.val p.2.2.val)=_
  rw [weightedFlag_eq_scaled_flag _ _ _ _ _ (ne_of_gt p.2.1.property) (ne_of_gt p.2.2.property),
    normalize_smul _ (mul_ne_zero (pow_ne_zero _ (ne_of_gt p.2.1.property))
      (pow_ne_zero _ (ne_of_gt p.2.2.property))),rootHomeomorph_symm]

/-- The primary detector is exactly the original trace-one form on the actual interior. -/
theorem A_embedding (S : Space) : A (cornerEmbedding S)=S.val := by
  have h := A_positive_parameters (rootHomeomorph S)
  change A (positiveCornerHomeomorph (rootHomeomorph S)).val=S.val
  simpa only [rootHomeomorph.symm_apply_apply] using h

end TernaryPoly.SymmetricSpaceCornerDegeneration
