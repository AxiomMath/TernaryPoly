module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.Coordinates

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpacePlaneBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

/-- The actual real block-parabolic parameters, including either sign of the last diagonal entry. -/
@[ext] structure Parameters where
  A : RealGL2
  u : Vec2
  d : ℝˣ

instance parameterOne : One Parameters := ⟨⟨1,0,1⟩⟩
instance parameterMul : Mul Parameters := ⟨fun p q =>
  ⟨p.A*q.A,p.A.val *ᵥ q.u+(q.d : ℝ) • p.u,p.d*q.d⟩⟩
instance parameterInv : Inv Parameters := ⟨fun p =>
  ⟨p.A⁻¹,-((p.d : ℝ)⁻¹ • ((p.A⁻¹).val *ᵥ p.u)),p.d⁻¹⟩⟩

def toRealGL (p : Parameters) : RealGL := parabolicGL p.A p.u p.d.val p.d.ne_zero

theorem toRealGL_injective : Function.Injective toRealGL := by
  intro p q h
  have hm : blockMatrix p.A.val p.u p.d.val=blockMatrix q.A.val q.u q.d.val :=
    congrArg (fun g : RealGL => g.val) h
  apply Parameters.ext
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun M : Mat => M 0 0) hm
    · exact congrArg (fun M : Mat => M 0 1) hm
    · exact congrArg (fun M : Mat => M 1 0) hm
    · exact congrArg (fun M : Mat => M 1 1) hm
  · ext i
    fin_cases i
    · exact congrArg (fun M : Mat => M 0 2) hm
    · exact congrArg (fun M : Mat => M 1 2) hm
  · apply Units.ext
    exact congrArg (fun M : Mat => M 2 2) hm

theorem blockMatrix_mul (A C : Mat2) (u w : Vec2) (d e : ℝ) :
    blockMatrix A u d*blockMatrix C w e=
      blockMatrix (A*C) (A *ᵥ w+e • u) (d*e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      smul_eq_mul] <;> ring

@[simp] theorem toRealGL_one : toRealGL 1=1 := by
  apply Units.ext
  change blockMatrix (1 : RealGL2).val 0 1=1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMatrix]

theorem toRealGL_mul (p q : Parameters) : toRealGL (p*q)=toRealGL p*toRealGL q := by
  apply Units.ext
  exact (blockMatrix_mul p.A.val q.A.val p.u q.u p.d.val q.d.val).symm

theorem parameters_inv_mul (p : Parameters) : p⁻¹*p=1 := by
  apply Parameters.ext
  · exact inv_mul_cancel p.A
  · change (p.A⁻¹).val *ᵥ p.u+(p.d : ℝ) •
      (-((p.d : ℝ)⁻¹ • ((p.A⁻¹).val *ᵥ p.u)))=0
    rw [smul_neg,smul_smul,mul_inv_cancel₀ p.d.ne_zero,one_smul,add_neg_cancel]
  · exact inv_mul_cancel p.d

/-- The group laws are proved by faithful multiplication of the actual block matrices. -/
instance parametersGroup : Group Parameters where
  mul := fun p q => ⟨p.A*q.A,p.A.val *ᵥ q.u+(q.d : ℝ) • p.u,p.d*q.d⟩
  one := ⟨1,0,1⟩
  inv := fun p => ⟨p.A⁻¹,-((p.d : ℝ)⁻¹ • ((p.A⁻¹).val *ᵥ p.u)),p.d⁻¹⟩
  mul_assoc p q r := toRealGL_injective (by simp only [toRealGL_mul,mul_assoc])
  one_mul p := toRealGL_injective (by rw [toRealGL_mul,toRealGL_one,one_mul])
  mul_one p := toRealGL_injective (by rw [toRealGL_mul,toRealGL_one,mul_one])
  inv_mul_cancel := parameters_inv_mul

/-- A faithful homomorphism into the genuine real GL3 action group. -/
def toRealGLHom : Parameters →* RealGL where
  toFun := toRealGL
  map_one' := toRealGL_one
  map_mul' := toRealGL_mul

@[simp] theorem toRealGL_inv (p : Parameters) : toRealGL p⁻¹=(toRealGL p)⁻¹ :=
  toRealGLHom.map_inv p

end TernaryPoly.SymmetricSpacePlaneBordification
