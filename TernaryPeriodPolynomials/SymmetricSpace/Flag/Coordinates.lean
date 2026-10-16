module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesBinary

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagCoordinates
open Matrix
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

abbrev Vec3 := Fin 3 → ℝ
abbrev LDLParameters := Vec3 × (PositiveScale × PositiveScale)

/-- The literal upper-unitriangular flag matrix, with coordinates in the order x,y,z. -/
def upper (x y z : ℝ) : Mat := !![1,x,z;0,1,y;0,0,1]

/-- Two positive diagonal pivots, with the third normalized to one. -/
def diagonal (a b : ℝ) : Mat := Matrix.diagonal ![a,b,1]

def flagMatrix (x y z a b : ℝ) : Mat := upper x y z*diagonal a b*(upper x y z).transpose

/-- The exact full-flag formula agrees with the existing plane Schur assembly. -/
theorem flagMatrix_eq_assemble (x y z a b : ℝ) :
    flagMatrix x y z a b=assemble ![z,y] (binaryLDL x a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flagMatrix,upper,diagonal,binaryLDL,assemble,Matrix.mul_apply,Matrix.vecMul_diagonal,Fin.sum_univ_succ]
  all_goals ring

/-- Positive flag pivots yield a genuinely positive-definite matrix. -/
theorem flagMatrix_positive (x y z a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (flagMatrix x y z a b).PosDef := by
  rw [flagMatrix_eq_assemble]
  exact assemble_positive _ _ (binaryLDL_positive x a b ha hb)

/-- The simple coordinate rearrangement from plane LDL data to full-flag data. -/
def rearrangeHomeomorph : (Vec2 × (ℝ × (PositiveScale × PositiveScale))) ≃ₜ LDLParameters where
  toFun p := (![p.2.1,p.1 1,p.1 0],p.2.2)
  invFun p := (![p.1 2,p.1 1],(p.1 0,p.2))
  left_inv p := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual trace-one positive space has unique continuous full-flag LDL coordinates. -/
def ldlHomeomorph : Space ≃ₜ LDLParameters :=
  (horosphericalHomeomorph.trans
    ((Homeomorph.refl Vec2).prodCongr binaryLDLHomeomorph)).trans rearrangeHomeomorph

@[simp] theorem ldlHomeomorph_unipotent (S : Space) :
    (ldlHomeomorph S).1=
      ![binaryX (schur S.val),unipotent S.val 1,unipotent S.val 0] := rfl

@[simp] theorem ldlHomeomorph_a (S : Space) :
    (ldlHomeomorph S).2.1.val=binaryA (schur S.val) := rfl

@[simp] theorem ldlHomeomorph_b (S : Space) :
    (ldlHomeomorph S).2.2.val=binaryB (schur S.val) := rfl

/-- The inverse is literally normalized upper-triangular congruence. -/
@[simp] theorem ldlHomeomorph_symm (p : LDLParameters) :
    (ldlHomeomorph.symm p).val=
      normalize (flagMatrix (p.1 0) (p.1 1) (p.1 2) p.2.1.val p.2.2.val) := by
  rw [flagMatrix_eq_assemble]
  rfl

/-- Existence and uniqueness are for the exact normalized matrix formula. -/
theorem normalizedFlag_exists_unique (S : Space) :
    ∃! p : LDLParameters,
      normalize (flagMatrix (p.1 0) (p.1 1) (p.1 2) p.2.1.val p.2.2.val)=S.val := by
  refine ⟨ldlHomeomorph S,?_,?_⟩
  · exact (ldlHomeomorph_symm (ldlHomeomorph S)).symm.trans
      (congrArg Subtype.val (ldlHomeomorph.symm_apply_apply S))
  · intro p hp
    apply ldlHomeomorph.symm.injective
    apply Subtype.ext
    rw [ldlHomeomorph.symm_apply_apply,ldlHomeomorph_symm]
    exact hp

end TernaryPoly.SymmetricSpaceFlagCoordinates
