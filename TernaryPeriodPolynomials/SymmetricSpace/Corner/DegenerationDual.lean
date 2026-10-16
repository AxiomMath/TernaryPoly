module

public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationPrimary
public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationFlagDuality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerDegeneration
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceLineBordification

theorem flip_conjugate_trace (M : Mat) : (conjugate flipGL M).trace=M.trace := by
  change (flipMatrix*M*star flipMatrix).trace=M.trace
  rw [flipMatrix_star,Matrix.trace_mul_cycle,flipMatrix_mul_self,Matrix.one_mul]

theorem flip_conjugate_normalize (M : Mat) :
    conjugate flipGL (SymmetricSpacePositive.normalize M)=
      SymmetricSpacePositive.normalize (conjugate flipGL M) := by
  rw [SymmetricSpacePositive.normalize,conjugate_smul,
    SymmetricSpacePositive.normalize,flip_conjugate_trace]

/-- The complementary degeneration detector, obtained by actual inverse-form duality. -/
def D (p : Corner) : Mat := conjugate flipGL (A (dualCorner p))

theorem D_psd (p : Corner) : (D p).PosSemidef := conjugate_psd flipGL (A_psd (dualCorner p))

@[simp] theorem D_trace (p : Corner) : (D p).trace=1 := by rw [D,flip_conjugate_trace,A_trace]

theorem D_ne_zero (p : Corner) : D p≠0 := conjugate_ne_zero flipGL (A_ne_zero (dualCorner p))

theorem continuous_D : Continuous D := by
  have hA := continuous_A.comp dualCornerHomeomorph.continuous
  exact (continuous_const.mul hA).mul continuous_const

def E22 : Mat := Matrix.diagonal ![0,0,1]

@[simp] theorem E22_trace : E22.trace=1 := by simp [E22,Matrix.trace,Fin.sum_univ_succ]

theorem flip_E00 : conjugate flipGL E00=E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugate,flipGL,flipMatrix,E00,E22,Matrix.mul_apply,Matrix.vecMul_diagonal,Fin.sum_univ_succ]

theorem D_t2_zero (p : Corner) (ht : p.2.2.val=0) : D p=E22 := by
  have hs : (dualCorner p).2.1.val=0 := ht
  rw [D,A_t1_zero _ hs,flip_E00]

/-- The dual detector is literally the normalized inverse of each interior form. -/
theorem D_embedding (S : Space) : D (cornerEmbedding S)=(inverseForm S).val := by
  rw [D,dualCorner_embedding,A_embedding]
  change conjugate flipGL (SymmetricSpacePositive.normalize
    (conjugate flipGL (inverseForm S).val))=(inverseForm S).val
  rw [flip_conjugate_normalize,←conjugate_mul,flipGL_mul_self,conjugate_one,
    normalize_of_trace_one _ (inverseForm S).property.2]

theorem D_embedding_inverse (S : Space) :
    D (cornerEmbedding S)=SymmetricSpacePositive.normalize S.val⁻¹ := D_embedding S

end TernaryPoly.SymmetricSpaceCornerDegeneration
