module

public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerGroup
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBorelCorner
open Matrix
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates

/-- The actual upper-triangular shear formulas on x,y,z. -/
def shear (g : BorelGroup) (v : Vec3) : Vec3 :=
  ![(g.val.val 0 0*v 0+g.val.val 0 1)/g.val.val 1 1,
    (g.val.val 1 1*v 1+g.val.val 1 2)/g.val.val 2 2,
    (g.val.val 0 0*v 2+g.val.val 0 1*v 1+g.val.val 0 2)/g.val.val 2 2]

/-- Full signed triangular congruence in the exact flag matrix model. -/
theorem upperMatrix_congruence (a b c d e f x y z A B : ℝ) (hd : d≠0) (hf : f≠0) :
    upperMatrix a b c d e f*flagMatrix x y z A B*star (upperMatrix a b c d e f)=
      f^2 • flagMatrix ((a*x+b)/d) ((d*y+e)/f) ((a*z+b*y+c)/f)
        ((a/f)^2*A) ((d/f)^2*B) := by
  simp only [flagMatrix_eq_assemble]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix,assemble,binaryLDL,Matrix.mul_apply,Fin.sum_univ_succ,
      smul_eq_mul,Matrix.star_eq_conjTranspose] <;> field_simp [hd,hf] <;> ring

theorem conjugate_flag (g : BorelGroup) (v : Vec3) (A B : ℝ) :
    conjugate g.val (flagMatrix (v 0) (v 1) (v 2) A B)=
      (g.val.val 2 2)^2 • flagMatrix (shear g v 0) (shear g v 1) (shear g v 2)
        ((g.val.val 0 0/g.val.val 2 2)^2*A) ((g.val.val 1 1/g.val.val 2 2)^2*B) := by
  change g.val.val*flagMatrix (v 0) (v 1) (v 2) A B*star g.val.val=_
  rw [matrix_eq_upper g]
  exact upperMatrix_congruence _ _ _ _ _ _ _ _ _ _ _
    (diagonal_nonzero g).2.1 (diagonal_nonzero g).2.2

/-- The five claimed action formulas on the positive root parameters. -/
def rootAction (g : BorelGroup) (p : RootParameters) : RootParameters :=
  (shear g p.1,(⟨factor1 g*p.2.1.val,mul_pos (factor1_pos g) p.2.1.property⟩,
    ⟨factor2 g*p.2.2.val,mul_pos (factor2_pos g) p.2.2.property⟩))

theorem rootAction_pivot1 (g : BorelGroup) (p : RootParameters) :
    ((rootAction g p).2.1.val^2*(rootAction g p).2.2.val^2)⁻¹=
      (g.val.val 0 0/g.val.val 2 2)^2*(p.2.1.val^2*p.2.2.val^2)⁻¹ := by
  obtain ⟨ha,hd,hf⟩ := diagonal_nonzero g
  have h1 : p.2.1.val≠0 := ne_of_gt p.2.1.property
  have h2 : p.2.2.val≠0 := ne_of_gt p.2.2.property
  simp only [rootAction,factor1,factor2,mul_pow,sq_abs,div_pow]
  field_simp

theorem rootAction_pivot2 (g : BorelGroup) (p : RootParameters) :
    ((rootAction g p).2.2.val^2)⁻¹=
      (g.val.val 1 1/g.val.val 2 2)^2*(p.2.2.val^2)⁻¹ := by
  obtain ⟨_,hd,hf⟩ := diagonal_nonzero g
  have h2 : p.2.2.val≠0 := ne_of_gt p.2.2.property
  simp only [rootAction,factor2,mul_pow,sq_abs,div_pow]
  field_simp

/-- Agreement of the root formulas with genuine normalized congruence on every positive form. -/
theorem act_rootHomeomorph_symm (g : BorelGroup) (p : RootParameters) :
    act g.val (rootHomeomorph.symm p)=rootHomeomorph.symm (rootAction g p) := by
  apply Subtype.ext
  change normalize (conjugate g.val (rootHomeomorph.symm p).val)=_
  rw [rootHomeomorph_symm,rootHomeomorph_symm]
  change normalize (conjugate g.val
    ((flagMatrix (p.1 0) (p.1 1) (p.1 2) (p.2.1.val^2*p.2.2.val^2)⁻¹ (p.2.2.val^2)⁻¹).trace⁻¹ •
      flagMatrix (p.1 0) (p.1 1) (p.1 2) (p.2.1.val^2*p.2.2.val^2)⁻¹ (p.2.2.val^2)⁻¹))=_
  rw [conjugate_smul,normalize_smul _ (inv_ne_zero (ne_of_gt
    (flagMatrix_positive _ _ _ _ _
      (inv_pos.mpr (mul_pos (pow_pos p.2.1.property 2) (pow_pos p.2.2.property 2)))
      (inv_pos.mpr (pow_pos p.2.2.property 2))).trace_pos)),
    conjugate_flag,normalize_smul _ (pow_ne_zero 2 (diagonal_nonzero g).2.2),
    rootAction_pivot1,rootAction_pivot2]
  rfl

theorem rootHomeomorph_act (g : BorelGroup) (S : Space) :
    rootHomeomorph (act g.val S)=rootAction g (rootHomeomorph S) := by
  apply rootHomeomorph.symm.injective
  rw [rootHomeomorph.symm_apply_apply,←act_rootHomeomorph_symm,rootHomeomorph.symm_apply_apply]

end TernaryPoly.SymmetricSpaceBorelCorner
