module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootModule
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantMatrices
public import TernaryPeriodPolynomials.Polynomial.PolynomialSupport
public import Mathlib.RepresentationTheory.Invariants

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCommonRoot
open ModThreeGoodAction PolynomialGLAction RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices MvPolynomial

/-- The actual common root subgroup `{I+aE13 : a ∈ ℤ}`. -/
def commonRoot : Subgroup IntegralGL where
  carrier := Set.range (rootElement 1)
  one_mem' := ⟨0, rootElement_zero 1⟩
  mul_mem' := by
    rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨a+b, (rootElement_mul 1 a b).symm⟩
  inv_mem' := by
    rintro _ ⟨a,rfl⟩
    exact ⟨-a, (rootElement_inv 1 a).symm⟩

/-- Its literal integral root elements. -/
def commonElement (a : ℤ) : commonRoot := ⟨rootElement 1 a, ⟨a,rfl⟩⟩

/-- The congruence root `I+3E13` fixes every residue covector. -/
theorem root_three_reduction : reduction (rootElement 1 3) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rootElement, bbMatrix, reduction, Matrix.GeneralLinearGroup.map_apply]
  decide

 theorem root_three_mem_K : rootElement 1 3 ∈ K := by
  change Matrix.vecMul fixedRow (reduction (rootElement 1 3)).val = fixedRow
  rw [root_three_reduction, Units.val_one, Matrix.vecMul_one]

/-- Determinant twists are literally trivial on this entire integral root subgroup. -/
theorem root_determinant (e : ℤ) (a : ℤ) :
    determinantCharacter e (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)
      (rootElement 1 a)) = 1 := by
  change (_ ^ e : ℚ) = 1
  have hd : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (rootElement 1 a)) : ℚˣ) : ℚ) = 1 := by
    simp [Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.map_apply,
      rootElement, bbMatrix, Matrix.det_fin_three]
  rw [hd, one_zpow]

/-- The inverse-action normalization is the shear `X0 ↦ X0-a X2`, for every twist. -/
theorem integralAction_common_root (n : ℕ) (e : ℤ) (a : ℤ) (p : HomogeneousPoly n) :
    (integralAction n e (rootElement 1 a) p : PolynomialGLAction.Poly) =
      RelativeEdgeCohomologyPolynomials.shearStep 0 2 a p := by
  rw [integralAction_coe, action_apply, root_determinant, one_smul, ← map_inv,
    rootElement_inv]
  have he : substitute (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)
      (rootElement 1 (-a))).val = RelativeEdgeCohomologyPolynomials.shearStep 0 2 a := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [substitute_X, linearForm, Matrix.map,
      rootElement, bbMatrix, Fin.sum_univ_three, sub_eq_add_neg]
  exact DFunLike.congr_fun he (p : PolynomialGLAction.Poly)

/-- The actual common-root representation on all 26 homogeneous fibers. -/
def commonRepresentation (n : ℕ) (e : ℤ) : Representation ℚ commonRoot (Coefficients n) :=
  (coefficientAction n e).comp commonRoot.subtype

/-- Every invariant of the actual common root has binary, hence pairwise, distinguished support. -/
theorem invariant_evaluation_pairwise (n : ℕ) (e : ℤ) (F : Coefficients n)
    (hF : F ∈ (commonRepresentation n e).invariants) :
    Pairwise (evaluation n F : PolynomialGLAction.Poly) := by
  have h := congrArg (fun H => (evaluation n H : PolynomialGLAction.Poly)) (hF (commonElement 3))
  change (evaluation n (coefficientAction n e (rootElement 1 3) F) : PolynomialGLAction.Poly) = _ at h
  rw [evaluation_action n e _ root_three_mem_K, integralAction_common_root] at h
  exact pairwise_of_first_shearStep_fixed 1 3 (by norm_num) h

end TernaryPoly.OrdinaryBoundaryCommonRoot
