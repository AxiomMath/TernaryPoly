module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyParity
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyGenerators
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantDiagonal

@[expose] public section

open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyActions
open RelativeStabilizerConsumer RelativeStabilizerParameters RelativeStabilizerMatrices
open RelativeEdgeCohomologyMatrices RelativeEdgeCohomologyPolynomials RadicalCoinvariantAlgebra

/-- The actual untwisted inverse-substitution coefficient representations. -/
abbrev bbRep (n : ℕ) : Rep.{0} ℚ HBBGroup :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp HBBGroup.subtype)

abbrev bgRep (n : ℕ) : Rep.{0} ℚ HBGGroup :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp HBGGroup.subtype)

/-- Erasure on the actual homogeneous coefficient module. -/
def eraseCoeff (n : ℕ) (j : Fin 3) : PolynomialGLAction.HomogeneousPoly n →ₗ[ℚ] Poly where
  toFun p := erase j p
  map_add' p q := map_add (erase j) (p : Poly) (q : Poly)
  map_smul' c p := map_smul (erase j).toLinearMap c (p : Poly)

lemma bb_action (n : ℕ) (k : Fin 3) (p : bbRep n) :
    (bbRep n).ρ (bbRoot k 1) p = homogeneousShear n (rootSource k) (rootTarget k) p := by
  change PolynomialGLAction.integralAction n 0 (rootElement k 1) p = _
  rw [integralAction_root]

lemma bb_action_coe (n : ℕ) (k : Fin 3) (p : bbRep n) :
    ((bbRep n).ρ (bbRoot k 1) p : Poly) = shear (rootSource k) (rootTarget k) p := by
  rw [bb_action]
  rfl

lemma bg_action_coe (n : ℕ) (k : Fin 3) (p : bgRep n) :
    ((bgRep n).ρ (bgRoot k 1) p : Poly) =
      shearStep (![0,2,0] k) (![2,1,1] k) (![1,3,1] k) p := by
  change (PolynomialGLAction.integralAction n 0 (bgRoot k 1).val p : Poly) = _
  rw [PolynomialGLAction.integralAction_coe, PolynomialGLAction.action_apply]
  simp only [PolynomialGLAction.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    zpow_zero, one_smul]
  rw [← map_inv]
  have hi : (bgRoot k 1).val⁻¹ = (bgRoot k (-1)).val :=
    congrArg Subtype.val (bgRoot_inv k 1)
  rw [hi]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  rw [PolynomialGLAction.substitute_X]
  fin_cases k <;> fin_cases i <;>
    simp [PolynomialGLAction.linearForm, GeneralLinearGroup.map_apply, bgRoot, bgMatrix,
      Fin.sum_univ_three, shearStep, sub_eq_add_neg, map_ofNat]
  ring

lemma bb_first_coe (n : ℕ) (p : bbRep n) :
    ((bbRep n).ρ bbFirst p : Poly) = flip 0 p := by
  change (PolynomialGLAction.integralAction n 0 (diagonalHom (-1,1)) p : Poly) = _
  rw [integralAction_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp [diagonalSubst, unitScalar, RelativeEdgeCohomologyPolynomials.flip]

lemma bb_second_coe (n : ℕ) (p : bbRep n) :
    ((bbRep n).ρ bbSecond p : Poly) = flip 1 p := by
  change (PolynomialGLAction.integralAction n 0 (diagonalHom (1,-1)) p : Poly) = _
  rw [integralAction_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp [diagonalSubst, unitScalar, RelativeEdgeCohomologyPolynomials.flip]

lemma bg_first_coe (n : ℕ) (p : bgRep n) :
    ((bgRep n).ρ bgFirst p : Poly) = flip 0 p := by
  change (PolynomialGLAction.integralAction n 0 (diagonalHom (-1,1)) p : Poly) = _
  rw [integralAction_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp [diagonalSubst, unitScalar, RelativeEdgeCohomologyPolynomials.flip]

lemma bg_second_coe (n : ℕ) (p : bgRep n) :
    ((bgRep n).ρ bgSecond p : Poly) = flip 1 p := by
  change (PolynomialGLAction.integralAction n 0 (diagonalHom (1,-1)) p : Poly) = _
  rw [integralAction_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp [diagonalSubst, unitScalar, RelativeEdgeCohomologyPolynomials.flip]

end TernaryPoly.RelativeEdgeCohomologyActions
