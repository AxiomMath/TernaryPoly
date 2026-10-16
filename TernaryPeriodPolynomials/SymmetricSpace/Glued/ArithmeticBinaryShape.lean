module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticBinaryBounds

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open SymmetricSpacePlaneBordification

/-- A polynomial positive binary shape with the actual root t. -/
def binaryWeighted (x t : ℝ) : Mat2 := !![1+x^2*t^2,x*t^2;x*t^2,t^2]

theorem binaryWeighted_scaled (x t : ℝ) (ht : t≠0) :
    binaryWeighted x t=t^2 • shapeMatrix x t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryWeighted,shapeMatrix_formula,Matrix.smul_apply,smul_eq_mul] <;> field_simp [ht]
  all_goals ring

theorem binaryWeighted_positive (x t : ℝ) (ht : 0<t) : (binaryWeighted x t).PosDef := by
  rw [binaryWeighted_scaled x t (ne_of_gt ht)]
  exact (shapeMatrix_positive x t ht).smul (sq_pos_of_pos ht)

/-- The normalized polynomial shape is the exact existing flag-overlap shape. -/
theorem binaryWeighted_normalize (x t : ℝ) (ht : 0<t) :
    binaryNormalize (binaryWeighted x t)=binaryNormalize (shapeMatrix x t) := by
  rw [binaryWeighted_scaled x t (ne_of_gt ht),binaryNormalize_smul _ (ne_of_gt (sq_pos_of_pos ht))]

/-- Actual normalized binary shape action yields a positive scalar congruence of polynomial shapes. -/
theorem binary_shape_scale (A : RealGL2) (x y t s : ℝ) (ht : 0<t) (hs : 0<s)
    (h : binaryNormalize (A.val*binaryNormalize (shapeMatrix x t)*star A.val)=
      binaryNormalize (shapeMatrix y s)) :
    ∃ k : ℝ,0<k ∧ A.val*binaryWeighted x t*star A.val=k • binaryWeighted y s := by
  let S := binaryWeighted x t
  let T := binaryWeighted y s
  let C := A.val*S*star A.val
  have hS : S.PosDef := binaryWeighted_positive x t ht
  have hT : T.PosDef := binaryWeighted_positive y s hs
  have hC : C.PosDef := A.isUnit.posDef_star_right_conjugate_iff.mpr hS
  have hn : binaryNormalize C=binaryNormalize T := by
    rw [←binaryWeighted_normalize x t ht,←binaryWeighted_normalize y s hs] at h
    change binaryNormalize (A.val*((S.trace)⁻¹ • S)*star A.val)=binaryNormalize T at h
    rw [Matrix.mul_smul,Matrix.smul_mul,binaryNormalize_smul _ (inv_ne_zero (ne_of_gt hS.trace_pos))] at h
    exact h
  refine ⟨C.trace/T.trace,div_pos hC.trace_pos hT.trace_pos,?_⟩
  have he := congrArg (fun M : Mat2 => C.trace • M) hn
  simpa only [binaryNormalize,smul_smul,mul_inv_cancel₀ (ne_of_gt hC.trace_pos),one_smul,
    div_eq_mul_inv] using he

/-- The actual binary positive-shape action satisfies the uniform rank-two Siegel bound. -/
theorem binary_shape_siegel_bound (δ D M : ℝ) (hδ : 0<δ) (hD : 0≤D) (hM : 1≤M) :
    ∃ R : ℝ,∀ (A : RealGL2) (x y t s : ℝ),0<t → 0<s →
      δ≤|A.val 1 0| → |A.val.det|≤D → |x|≤M → |y|≤M → t≤M → s≤M →
      binaryNormalize (A.val*binaryNormalize (shapeMatrix x t)*star A.val)=
        binaryNormalize (shapeMatrix y s) → ∀ i j,|A.val i j|≤R := by
  obtain ⟨R,hR⟩ := binary_siegel_entry_bound δ D M hδ hD hM
  refine ⟨R,?_⟩
  intro A x y t s ht hs hc hdet hx hy htm hsm he
  obtain ⟨k,hk,hkmat⟩ := binary_shape_scale A x y t s ht hs he
  have h00 : A.val 0 0^2+t^2*(A.val 0 0*x+A.val 0 1)^2=k*(1+y^2*s^2) := by
    have h := congrArg (fun T : Mat2 => T 0 0) hkmat
    simp [binaryWeighted,Matrix.mul_apply,Fin.sum_univ_succ,smul_eq_mul] at h
    nlinarith only [h]
  have h01 : A.val 0 0*A.val 1 0+t^2*(A.val 0 0*x+A.val 0 1)*(A.val 1 0*x+A.val 1 1)=k*y*s^2 := by
    have h := congrArg (fun T : Mat2 => T 0 1) hkmat
    simp [binaryWeighted,Matrix.mul_apply,Fin.sum_univ_succ,smul_eq_mul] at h
    nlinarith only [h]
  have h11 : A.val 1 0^2+t^2*(A.val 1 0*x+A.val 1 1)^2=k*s^2 := by
    have h := congrArg (fun T : Mat2 => T 1 1) hkmat
    simp [binaryWeighted,Matrix.mul_apply,Fin.sum_univ_succ,smul_eq_mul] at h
    nlinarith only [h]
  have hh := hR (A.val 0 0) (A.val 0 1) (A.val 1 0) (A.val 1 1) x y t s k
    ht hs hk hc (by simpa only [det_fin_two] using hdet) hx hy htm hsm h00 h01 h11
  intro i j
  fin_cases i <;> fin_cases j
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2.1
  · exact hh.2.2.2

end TernaryPoly.SymmetricSpaceGluedArithmetic
