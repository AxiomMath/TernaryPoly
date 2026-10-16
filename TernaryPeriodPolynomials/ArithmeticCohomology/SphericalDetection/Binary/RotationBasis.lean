module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.MonomialBasis
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binarySubstitutionEquiv (degree : ℕ) (matrix : Binary.GL2) :
    Binary.HomogeneousPoly degree ≃ₗ[ℂ] Binary.HomogeneousPoly degree where
  toFun polynomial := ⟨Binary.substitute matrix.val polynomial.val,
    Binary.substitute_homogeneous matrix.val polynomial.property⟩
  invFun polynomial := ⟨Binary.substitute matrix⁻¹.val polynomial.val,
    Binary.substitute_homogeneous matrix⁻¹.val polynomial.property⟩
  left_inv polynomial := by
    apply Subtype.ext
    change Binary.substitute matrix⁻¹.val (Binary.substitute matrix.val polynomial.val) = polynomial.val
    rw [← AlgHom.comp_apply, Binary.substitute_comp, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Binary.substitute_one]
    rfl
  right_inv polynomial := by
    apply Subtype.ext
    change Binary.substitute matrix.val (Binary.substitute matrix⁻¹.val polynomial.val) = polynomial.val
    rw [← AlgHom.comp_apply, Binary.substitute_comp, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Binary.substitute_one]
    rfl
  map_add' first second := Subtype.ext (map_add (Binary.substitute matrix.val) first.val second.val)
  map_smul' scalar polynomial := Subtype.ext (map_smul (Binary.substitute matrix.val) scalar polynomial.val)

def binaryComplexCoordinates : Binary.GL2 where
  val := !![1, Complex.I; 1, -Complex.I]
  inv := !![1/2, 1/2; -Complex.I/2, Complex.I/2]
  val_inv := by
    ext row column
    fin_cases row <;> fin_cases column
    all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals norm_num [Complex.I_sq]
  inv_val := by
    ext row column
    fin_cases row <;> fin_cases column
    all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals norm_num [Complex.I_sq]

def binaryRotationBasis (degree : ℕ) :
    Module.Basis (BinaryHomogeneousExponent degree) ℂ (Binary.HomogeneousPoly degree) :=
  (binaryMonomialBasis degree).map (binarySubstitutionEquiv degree binaryComplexCoordinates)

theorem binaryRotationBasis_coe (degree : ℕ) (exponent : BinaryHomogeneousExponent degree) :
    (binaryRotationBasis degree exponent).val =
      Binary.substitute binaryComplexCoordinates.val (monomial exponent.val (1 : ℂ)) := by
  change Binary.substitute binaryComplexCoordinates.val (binaryMonomialBasis degree exponent).val = _
  rw [binaryMonomialBasis_coe]

theorem binarySubstitute_diagonal_monomial (diagonal : Fin 2 → ℂ) (exponent : Fin 2 →₀ ℕ) :
    Binary.substitute (Matrix.diagonal diagonal) (monomial exponent (1 : ℂ)) =
      (diagonal 0 ^ exponent 0 * diagonal 1 ^ exponent 1) • monomial exponent (1 : ℂ) := by
  have generator (position : Fin 2) : Binary.linearForm (Matrix.diagonal diagonal) position =
      C (diagonal position) * X position := by
    fin_cases position <;> simp [Binary.linearForm, Matrix.diagonal_apply]
  simp only [Binary.substitute, bind₁_monomial, generator, map_one, one_mul, mul_pow]
  rw [Finset.prod_mul_distrib]
  have scalar_product : (∏ position ∈ exponent.support, (C (diagonal position) : Binary.Poly) ^ exponent position) =
      C (diagonal 0 ^ exponent 0 * diagonal 1 ^ exponent 1) := by
    simp only [← map_pow, ← map_prod]
    congr 1
    change exponent.prod (fun position power => diagonal position ^ power) = _
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rw [scalar_product, Algebra.smul_def, monomial_eq]
  simp only [map_one, one_mul]
  rfl

theorem binaryComplexCoordinates_rotation (angle : Circle) :
    binaryComplexCoordinates.val * (GeneralLinearGroup.map (algebraMap ℝ ℂ) (binaryRotations angle))⁻¹.val =
      Matrix.diagonal ![(angle : ℂ)⁻¹, (angle : ℂ)] * binaryComplexCoordinates.val := by
  rw [← map_inv, GeneralLinearGroup.val_map_apply]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryComplexCoordinates, binaryRotations, binaryRotation, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply] <;>
    apply Complex.ext <;> simp

theorem binaryRotationBasis_coefficient (degree : ℕ) (angle : Circle)
    (exponent : BinaryHomogeneousExponent (degree + 1)) :
    binaryCoefficient degree (binaryRotations angle) (binaryRotationBasis (degree + 1) exponent) =
      (((angle : ℂ)⁻¹) ^ exponent.val 0 * (angle : ℂ) ^ exponent.val 1) •
        binaryRotationBasis (degree + 1) exponent := by
  have determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) (binaryRotations angle))).val = 1 := by
    exact (Complex.ofRealHom.map_det (binaryRotationMatrix angle)).symm.trans
      (by rw [binaryRotationMatrix_det, map_one])
  apply Subtype.ext
  simp only [binaryCoefficient, Binary.homogeneousAction_coe, Binary.action_apply,
    Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, determinant,
    one_zpow, one_smul, Submodule.coe_smul, binaryRotationBasis_coe]
  rw [← AlgHom.comp_apply, Binary.substitute_comp, binaryComplexCoordinates_rotation,
    ← Binary.substitute_comp, AlgHom.comp_apply, binarySubstitute_diagonal_monomial, map_smul]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
