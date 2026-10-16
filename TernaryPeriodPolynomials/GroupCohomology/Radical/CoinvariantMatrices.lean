module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantQuotients
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Parameters

@[expose] public section

open MvPolynomial Matrix

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The literal integral root matrices, ordered `I+tE12`, `I+tE13`, `I+tE23`. -/
def rootElement (k : Fin 3) (t : ℤ) : ModThreeGoodAction.IntegralGL :=
  ![bbElement 1 1 t 0 0, bbElement 1 1 0 t 0, bbElement 1 1 0 0 t] k

def rootSource (k : Fin 3) : Fin 3 := ![0,0,1] k
def rootTarget (k : Fin 3) : Fin 3 := ![1,2,2] k

theorem rootElement_zero (k : Fin 3) : rootElement k 0 = 1 := by
  apply Units.ext
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rootElement, bbMatrix]

theorem rootElement_mul (k : Fin 3) (s t : ℤ) :
    rootElement k s * rootElement k t = rootElement k (s+t) := by
  apply Units.ext
  rw [Units.val_mul]
  fin_cases k <;> ext i j <;> rw [Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [rootElement, bbMatrix, Fin.sum_univ_three, add_comm]

theorem rootElement_inv (k : Fin 3) (t : ℤ) :
    (rootElement k t)⁻¹ = rootElement k (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [rootElement_mul, add_neg_cancel, rootElement_zero]

theorem root_substitute (k : Fin 3) :
    PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (rootElement k (-1))).val =
      shear (rootSource k) (rootTarget k) := by
  ext i
  rw [PolynomialGLAction.substitute_X]
  fin_cases k <;> fin_cases i <;>
    simp [PolynomialGLAction.linearForm, GeneralLinearGroup.map_apply,
      rootElement, rootSource, rootTarget, bbMatrix, Fin.sum_univ_three, shear,
      sub_eq_add_neg]

/-- The existing coefficient representation really acts by the literal shear substitutions. -/
theorem integralAction_root (n : ℕ) (k : Fin 3) :
    PolynomialGLAction.integralAction n 0 (rootElement k 1) =
      homogeneousShear n (rootSource k) (rootTarget k) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  rw [PolynomialGLAction.integralAction_coe, PolynomialGLAction.action_apply]
  simp only [PolynomialGLAction.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    zpow_zero, one_smul]
  rw [← map_inv, rootElement_inv]
  exact DFunLike.congr_fun (root_substitute k) (p : Poly)

theorem rootElement_plane_first : rootElement 1 1 = planeElement 1 ![1,0] := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootElement, planeMatrix, bbMatrix]

theorem rootElement_plane_second : rootElement 2 1 = planeElement 1 ![0,1] := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootElement, planeMatrix, bbMatrix]

theorem rootElement_line_first : rootElement 0 1 = lineElement 1 ![1,0] 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootElement, lineMatrix, bbMatrix]

theorem rootElement_line_second : rootElement 1 1 = lineElement 1 ![0,1] 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootElement, lineMatrix, bbMatrix]

def actualPlaneRelations (n : ℕ) : Submodule ℚ (H n) :=
  LinearMap.range (PolynomialGLAction.integralAction n 0 (rootElement 1 1) - LinearMap.id) ⊔
  LinearMap.range (PolynomialGLAction.integralAction n 0 (rootElement 2 1) - LinearMap.id)

def actualLineRelations (n : ℕ) : Submodule ℚ (H n) :=
  LinearMap.range (PolynomialGLAction.integralAction n 0 (rootElement 0 1) - LinearMap.id) ⊔
  LinearMap.range (PolynomialGLAction.integralAction n 0 (rootElement 1 1) - LinearMap.id)

theorem actualPlaneRelations_eq (n : ℕ) : actualPlaneRelations n = planeRelations n := by
  simp [actualPlaneRelations, integralAction_root, rootSource, rootTarget, planeRelations,
    difference]

theorem actualLineRelations_eq (n : ℕ) : actualLineRelations n = lineRelations n := by
  simp [actualLineRelations, integralAction_root, rootSource, rootTarget, lineRelations,
    difference]

def actualPlaneQuotientEquiv (n : ℕ) : (H n ⧸ actualPlaneRelations n) ≃ₗ[ℚ] BinaryH n :=
  (Submodule.quotEquivOfEq _ _ (actualPlaneRelations_eq n)).trans (planeQuotientEquiv n)

def actualLineQuotientEquiv (n : ℕ) : (H n ⧸ actualLineRelations n) ≃ₗ[ℚ] UnaryH n :=
  (Submodule.quotEquivOfEq _ _ (actualLineRelations_eq n)).trans (lineQuotientEquiv n)

end TernaryPoly.RadicalCoinvariantAlgebra
