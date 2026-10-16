module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Unipotent

@[expose] public section



/-! Actual ring-general Levi block embeddings for the associate maximal parabolics. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open Matrix
variable {R : Type*} [CommRing R]

/-- The literal (2,1) block diagonal matrix. -/
def planeBlock (A : Matrix (Fin 2) (Fin 2) R) (d : R) : Matrix (Fin 3) (Fin 3) R :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, d]

theorem planeBlock_mul (A B : Matrix (Fin 2) (Fin 2) R) (d e : R) :
    planeBlock (A*B) (d*e) = planeBlock A d * planeBlock B e := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

@[simp] theorem planeBlock_one : planeBlock (1 : Matrix (Fin 2) (Fin 2) R) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The genuine block diagonal Levi element attached to an actual GL2 matrix and scalar unit. -/
def planeLevi (A : GeneralLinearGroup (Fin 2) R) (d : Rˣ) : GL3 R where
  val := planeBlock A.val d.val
  inv := planeBlock A.inv d.inv
  val_inv := by rw [← planeBlock_mul, A.val_inv, d.val_inv, planeBlock_one]
  inv_val := by rw [← planeBlock_mul, A.inv_val, d.inv_val, planeBlock_one]

/-- The actual (2,1) Levi embedding is multiplicative. -/
def planeLeviHom (R : Type*) [CommRing R] :
    (GeneralLinearGroup (Fin 2) R × Rˣ) →* GL3 R where
  toFun a := planeLevi a.1 a.2
  map_one' := Units.ext planeBlock_one
  map_mul' a b := Units.ext (planeBlock_mul a.1.val b.1.val a.2.val b.2.val)

/-- The actual plane Levi lies in the actual plane parabolic. -/
theorem planeLevi_mem (A : GeneralLinearGroup (Fin 2) R) (d : Rˣ) :
    planeLevi A d ∈ planeParabolic R := ⟨rfl, rfl⟩

/-- The associate line Levi, with the same exact Weyl convention as the standard integral. -/
def lineLevi (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R) : GL3 R :=
  weyl * planeLevi A d * weyl⁻¹

/-- The actual line Levi has scalar first block and GL2 last block. -/
theorem lineLevi_val (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R) :
    (lineLevi d A).val = !![d.val,0,0;0,A.val 0 0,A.val 0 1;0,A.val 1 0,A.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLevi, planeLevi, planeBlock, weyl, Matrix.mul_apply, Fin.sum_univ_three]

/-- The actual line Levi lies in the actual line parabolic. -/
theorem lineLevi_mem (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R) :
    lineLevi d A ∈ lineParabolic R := by
  change (lineLevi d A).val 1 0 = 0 ∧ (lineLevi d A).val 2 0 = 0
  rw [lineLevi_val]
  exact ⟨rfl, rfl⟩

/-- The literal associate-Levi matrix relation used to move inducing covariance across the Weyl. -/
theorem weyl_inverse_lineLevi (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R) :
    weyl⁻¹ * lineLevi d A = planeLevi A d * weyl⁻¹ := by
  simp [lineLevi, ← mul_assoc]

/-- The genuine line-Levi embedding is multiplicative. -/
def lineLeviHom (R : Type*) [CommRing R] :
    (Rˣ × GeneralLinearGroup (Fin 2) R) →* GL3 R where
  toFun a := lineLevi a.1 a.2
  map_one' := by
    change weyl * planeLevi 1 1 * weyl⁻¹ = 1
    have h : (planeLevi (1 : GeneralLinearGroup (Fin 2) R) 1) = 1 :=
      (planeLeviHom R).map_one
    rw [h, mul_one, mul_inv_cancel]
  map_mul' a b := by
    change weyl * planeLevi (a.2*b.2) (a.1*b.1) * weyl⁻¹ = _
    have h := (planeLeviHom R).map_mul (a.2,a.1) (b.2,b.1)
    change planeLevi (a.2*b.2) (a.1*b.1) = planeLevi a.2 a.1 * planeLevi b.2 b.1 at h
    rw [h]
    simp [lineLevi, mul_assoc]

end GeneralEisenstein.Adelic

end
