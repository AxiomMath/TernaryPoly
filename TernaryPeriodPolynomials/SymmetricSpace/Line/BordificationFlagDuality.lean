module

public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationPermutation
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLineBordification
open Matrix
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates

/-- The exact matrix formula for the permuted normalized inverse form. -/
theorem dualForm_val (S : Space) :
    (dualForm S).val=normalize (flipMatrix*S.val⁻¹*flipMatrix) := by
  change normalize (conjugate flipGL (normalize S.val⁻¹))=_
  change normalize (conjugate flipGL ((S.val⁻¹).trace⁻¹ • S.val⁻¹))=_
  rw [conjugate_smul,normalize_smul _ (inv_ne_zero (ne_of_gt S.property.1.inv.trace_pos))]
  change normalize (flipMatrix*S.val⁻¹*star flipMatrix)=_
  rw [flipMatrix_star]

/-- The inverse of the exact full-flag matrix, with both nonzero pivots explicit. -/
theorem flagMatrix_inverse (x y z a b : ℝ) (ha : a≠0) (hb : b≠0) :
    (flagMatrix x y z a b)⁻¹=
      flipMatrix*(a⁻¹ • flagMatrix (-y) (-x) (x*y-z) a (a/b))*flipMatrix := by
  apply Matrix.inv_eq_right_inv
  simp only [flagMatrix_eq_assemble]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [assemble,binaryLDL,flipMatrix,Matrix.mul_apply,
      Fin.sum_univ_succ,smul_eq_mul] <;> field_simp [ha,hb] <;> ring

/-- The permuted duality exchanges the two positive simple roots. -/
def dualRoot (p : RootParameters) : RootParameters :=
  (![-p.1 1,-p.1 0,p.1 0*p.1 1-p.1 2],(p.2.2,p.2.1))

@[simp] theorem dualRoot_involutive (p : RootParameters) : dualRoot (dualRoot p)=p := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [dualRoot]
    ring
  · rfl

theorem dualForm_root (p : RootParameters) :
    dualForm (rootHomeomorph.symm p)=rootHomeomorph.symm (dualRoot p) := by
  have h1 : 0<p.2.1.val := p.2.1.property
  have h2 : 0<p.2.2.val := p.2.2.property
  have ha : 0<(p.2.1.val^2*p.2.2.val^2)⁻¹ := inv_pos.mpr (mul_pos (pow_pos h1 2) (pow_pos h2 2))
  have hb : 0<(p.2.2.val^2)⁻¹ := inv_pos.mpr (pow_pos h2 2)
  have hdiv : (p.2.1.val^2*p.2.2.val^2)⁻¹/(p.2.2.val^2)⁻¹=(p.2.1.val^2)⁻¹ := by
    field_simp [ne_of_gt h1,ne_of_gt h2]
  apply Subtype.ext
  rw [dualForm_val,rootHomeomorph_symm,
    inv_normalize _ (flagMatrix_positive _ _ _ _ _ ha hb)]
  rw [Matrix.mul_smul,Matrix.smul_mul,normalize_smul _
    (ne_of_gt (flagMatrix_positive _ _ _ _ _ ha hb).trace_pos)]
  rw [flagMatrix_inverse _ _ _ _ _ (ne_of_gt ha) (ne_of_gt hb)]
  simp only [←Matrix.mul_assoc,flipMatrix_mul_self,Matrix.one_mul]
  rw [Matrix.mul_assoc,flipMatrix_mul_self,Matrix.mul_one,
    normalize_smul _ (inv_ne_zero (ne_of_gt ha)),hdiv,rootHomeomorph_symm]
  congr 1
  simp [dualRoot,mul_comm]

/-- The same polynomial shear involution is defined on the full closed flag corner. -/
def dualCorner (p : Corner) : Corner :=
  (![-p.1 1,-p.1 0,p.1 0*p.1 1-p.1 2],(p.2.2,p.2.1))

@[simp] theorem dualCorner_involutive (p : Corner) : dualCorner (dualCorner p)=p := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [dualCorner]
    ring
  · rfl

def dualCornerHomeomorph : Corner ≃ₜ Corner where
  toFun := dualCorner
  invFun := dualCorner
  left_inv := dualCorner_involutive
  right_inv := dualCorner_involutive
  continuous_toFun := by fun_prop [dualCorner]
  continuous_invFun := by fun_prop [dualCorner]

/-- Agreement of the corner involution with the actual duality on every positive form. -/
theorem dualCorner_embedding (S : Space) : dualCorner (cornerEmbedding S)=cornerEmbedding (dualForm S) := by
  obtain ⟨p,rfl⟩ := rootHomeomorph.symm.surjective S
  rw [dualForm_root]
  simp only [cornerEmbedding,cornerHomeomorph,Homeomorph.trans_apply,
    rootHomeomorph.apply_symm_apply]
  rfl

end TernaryPoly.SymmetricSpaceLineBordification
