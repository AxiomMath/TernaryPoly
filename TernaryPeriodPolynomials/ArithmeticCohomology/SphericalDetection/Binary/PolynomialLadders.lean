module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineCoefficientDerivative
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationBasis

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryInfinitesimalDerivation (matrix : Matrix (Fin 2) (Fin 2) ℂ) :
    Derivation ℂ Binary.Poly Binary.Poly :=
  ∑ position, Binary.linearForm matrix position • pderiv position

theorem binaryInfinitesimalDerivation_apply (matrix : Matrix (Fin 2) (Fin 2) ℂ) (polynomial : Binary.Poly) :
    binaryInfinitesimalDerivation matrix polynomial = binaryInfinitesimalSubstitution matrix polynomial := by
  simp [binaryInfinitesimalDerivation, binaryInfinitesimalSubstitution, smul_eq_mul]

def binaryInfinitesimalRotation : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def binaryPolynomialLowering : Derivation ℂ Binary.Poly Binary.Poly :=
  binaryInfinitesimalDerivation (binaryAffineInverseDerivative 1) -
    Complex.I • binaryInfinitesimalDerivation (binaryAffineInverseDerivative Complex.I) +
      (1 / 2 : ℂ) • binaryInfinitesimalDerivation binaryInfinitesimalRotation

def binaryPolynomialRaising : Derivation ℂ Binary.Poly Binary.Poly :=
  binaryInfinitesimalDerivation (binaryAffineInverseDerivative 1) +
    Complex.I • binaryInfinitesimalDerivation (binaryAffineInverseDerivative Complex.I) +
      (1 / 2 : ℂ) • binaryInfinitesimalDerivation binaryInfinitesimalRotation

def binaryPositiveCoordinate : Binary.Poly := X 0 + C Complex.I * X 1

def binaryNegativeCoordinate : Binary.Poly := X 0 - C Complex.I * X 1

theorem binary_half_constant : C (2⁻¹ : ℂ) + C (2⁻¹ : ℂ) = (1 : Binary.Poly) := by
  rw [← map_add]
  norm_num

theorem binaryPolynomialLowering_positive : binaryPolynomialLowering binaryPositiveCoordinate = 0 := by
  simp [binaryPolynomialLowering, binaryPositiveCoordinate, binaryInfinitesimalDerivation,
    binaryAffineInverseDerivative, binaryInfinitesimalRotation, Binary.linearForm, Fin.sum_univ_two,
    Algebra.smul_def, Derivation.leibniz]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one, neg_div, one_div]
  linear_combination X 1 * binary_half_constant

theorem binaryPolynomialLowering_negative :
    binaryPolynomialLowering binaryNegativeCoordinate = Complex.I • binaryPositiveCoordinate := by
  simp [binaryPolynomialLowering, binaryPositiveCoordinate, binaryNegativeCoordinate, binaryInfinitesimalDerivation,
    binaryAffineInverseDerivative, binaryInfinitesimalRotation, Binary.linearForm, Fin.sum_univ_two,
    Algebra.smul_def, Derivation.leibniz]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one, neg_div, one_div]
  linear_combination C Complex.I * X 0 * binary_half_constant

theorem binaryPolynomialRaising_positive :
    binaryPolynomialRaising binaryPositiveCoordinate = -Complex.I • binaryNegativeCoordinate := by
  simp [binaryPolynomialRaising, binaryPositiveCoordinate, binaryNegativeCoordinate, binaryInfinitesimalDerivation,
    binaryAffineInverseDerivative, binaryInfinitesimalRotation, Binary.linearForm, Fin.sum_univ_two,
    Algebra.smul_def, Derivation.leibniz]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one, neg_div, one_div]
  linear_combination -(C Complex.I * X 0) * binary_half_constant

theorem binaryPolynomialRaising_negative : binaryPolynomialRaising binaryNegativeCoordinate = 0 := by
  simp [binaryPolynomialRaising, binaryNegativeCoordinate, binaryInfinitesimalDerivation,
    binaryAffineInverseDerivative, binaryInfinitesimalRotation, Binary.linearForm, Fin.sum_univ_two,
    Algebra.smul_def, Derivation.leibniz]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one, neg_div, one_div]
  linear_combination X 1 * binary_half_constant

theorem binaryPolynomialLowering_monomial (first second : ℕ) :
    binaryPolynomialLowering (binaryPositiveCoordinate ^ first * binaryNegativeCoordinate ^ second) =
      (Complex.I * (second : ℂ)) • (binaryPositiveCoordinate ^ (first + 1) * binaryNegativeCoordinate ^ (second - 1)) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow,
    binaryPolynomialLowering_positive, binaryPolynomialLowering_negative]
  have nat_map (number : ℕ) : (algebraMap ℕ Binary.Poly) number = (number : Binary.Poly) := map_natCast _ number
  simp only [Algebra.smul_def, pow_succ, map_mul, map_natCast, Algebra.algebraMap_self_apply, nat_map]
  ring

theorem binaryPolynomialRaising_monomial (first second : ℕ) :
    binaryPolynomialRaising (binaryPositiveCoordinate ^ first * binaryNegativeCoordinate ^ second) =
      (-Complex.I * (first : ℂ)) • (binaryPositiveCoordinate ^ (first - 1) * binaryNegativeCoordinate ^ (second + 1)) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow,
    binaryPolynomialRaising_positive, binaryPolynomialRaising_negative]
  have nat_map (number : ℕ) : (algebraMap ℕ Binary.Poly) number = (number : Binary.Poly) := map_natCast _ number
  simp only [Algebra.smul_def, pow_succ, map_mul, map_natCast, map_neg, Algebra.algebraMap_self_apply, nat_map]
  ring

theorem binaryRotationBasis_coordinates (degree : ℕ) (exponent : BinaryHomogeneousExponent degree) :
    (binaryRotationBasis degree exponent).val =
      binaryPositiveCoordinate ^ exponent.val 0 * binaryNegativeCoordinate ^ exponent.val 1 := by
  rw [binaryRotationBasis_coe]
  simp only [Binary.substitute, bind₁_monomial, map_one, one_mul]
  change exponent.val.prod (fun position power => (Binary.linearForm binaryComplexCoordinates.val position) ^ power) = _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [Binary.linearForm, binaryComplexCoordinates, binaryPositiveCoordinate, binaryNegativeCoordinate, sub_eq_add_neg]

theorem binaryInfinitesimalRotation_positive :
    binaryInfinitesimalDerivation binaryInfinitesimalRotation binaryPositiveCoordinate =
      -Complex.I • binaryPositiveCoordinate := by
  simp [binaryInfinitesimalDerivation, binaryInfinitesimalRotation, Binary.linearForm,
    binaryPositiveCoordinate, Fin.sum_univ_two, Algebra.smul_def, Derivation.leibniz]
  ring_nf
  simp [← map_pow]

theorem binaryInfinitesimalRotation_negative :
    binaryInfinitesimalDerivation binaryInfinitesimalRotation binaryNegativeCoordinate =
      Complex.I • binaryNegativeCoordinate := by
  simp [binaryInfinitesimalDerivation, binaryInfinitesimalRotation, Binary.linearForm,
    binaryNegativeCoordinate, Fin.sum_univ_two, Algebra.smul_def, Derivation.leibniz]
  ring_nf
  simp [← map_pow]

theorem binaryDerivation_pow_eigenvector (derivation : Derivation ℂ Binary.Poly Binary.Poly)
    (polynomial : Binary.Poly) (scalar : ℂ) (eigenvector : derivation polynomial = scalar • polynomial)
    (power : ℕ) : derivation (polynomial ^ power) = ((power : ℂ) * scalar) • polynomial ^ power := by
  induction power with
  | zero => simp
  | succ power induction =>
    rw [pow_succ, Derivation.leibniz, induction, eigenvector]
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, Nat.cast_add, Nat.cast_one, map_mul, map_add,
      map_natCast, map_one]
    ring

theorem binaryInfinitesimalRotation_monomial (first second : ℕ) :
    binaryInfinitesimalDerivation binaryInfinitesimalRotation
        (binaryPositiveCoordinate ^ first * binaryNegativeCoordinate ^ second) =
      (Complex.I * ((second : ℂ) - (first : ℂ))) •
        (binaryPositiveCoordinate ^ first * binaryNegativeCoordinate ^ second) := by
  rw [Derivation.leibniz,
    binaryDerivation_pow_eigenvector _ _ _ binaryInfinitesimalRotation_positive,
    binaryDerivation_pow_eigenvector _ _ _ binaryInfinitesimalRotation_negative]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_mul, map_neg, map_sub, map_natCast]
  ring

theorem binaryRotationBasis_infinitesimalRotation (degree : ℕ) (exponent : BinaryHomogeneousExponent degree) :
    binaryInfinitesimalSubstitution binaryInfinitesimalRotation (binaryRotationBasis degree exponent).val =
      (Complex.I * ((exponent.val 1 : ℂ) - (exponent.val 0 : ℂ))) • (binaryRotationBasis degree exponent).val := by
  rw [← binaryInfinitesimalDerivation_apply, binaryRotationBasis_coordinates]
  exact binaryInfinitesimalRotation_monomial _ _

theorem binaryRotationBasis_lowering (degree : ℕ) (exponent : BinaryHomogeneousExponent degree) :
    binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1) (binaryRotationBasis degree exponent).val -
        Complex.I • binaryInfinitesimalSubstitution (binaryAffineInverseDerivative Complex.I) (binaryRotationBasis degree exponent).val +
        (Complex.I * ((exponent.val 1 : ℂ) - (exponent.val 0 : ℂ)) / 2) • (binaryRotationBasis degree exponent).val =
      (Complex.I * (exponent.val 1 : ℂ)) •
        (binaryPositiveCoordinate ^ (exponent.val 0 + 1) * binaryNegativeCoordinate ^ (exponent.val 1 - 1)) := by
  have equality := binaryPolynomialLowering_monomial (exponent.val 0) (exponent.val 1)
  rw [← binaryRotationBasis_coordinates degree exponent] at equality
  change binaryInfinitesimalDerivation (binaryAffineInverseDerivative 1) (binaryRotationBasis degree exponent).val -
      Complex.I • binaryInfinitesimalDerivation (binaryAffineInverseDerivative Complex.I) (binaryRotationBasis degree exponent).val +
      (1 / 2 : ℂ) • binaryInfinitesimalDerivation binaryInfinitesimalRotation (binaryRotationBasis degree exponent).val = _ at equality
  simp only [binaryInfinitesimalDerivation_apply, binaryRotationBasis_infinitesimalRotation, smul_smul] at equality
  convert equality using 1
  congr 1
  congr 1
  ring

theorem binaryRotationBasis_raising (degree : ℕ) (exponent : BinaryHomogeneousExponent degree) :
    binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1) (binaryRotationBasis degree exponent).val +
        Complex.I • binaryInfinitesimalSubstitution (binaryAffineInverseDerivative Complex.I) (binaryRotationBasis degree exponent).val +
        (Complex.I * ((exponent.val 1 : ℂ) - (exponent.val 0 : ℂ)) / 2) • (binaryRotationBasis degree exponent).val =
      (-Complex.I * (exponent.val 0 : ℂ)) •
        (binaryPositiveCoordinate ^ (exponent.val 0 - 1) * binaryNegativeCoordinate ^ (exponent.val 1 + 1)) := by
  have equality := binaryPolynomialRaising_monomial (exponent.val 0) (exponent.val 1)
  rw [← binaryRotationBasis_coordinates degree exponent] at equality
  change binaryInfinitesimalDerivation (binaryAffineInverseDerivative 1) (binaryRotationBasis degree exponent).val +
      Complex.I • binaryInfinitesimalDerivation (binaryAffineInverseDerivative Complex.I) (binaryRotationBasis degree exponent).val +
      (1 / 2 : ℂ) • binaryInfinitesimalDerivation binaryInfinitesimalRotation (binaryRotationBasis degree exponent).val = _ at equality
  simp only [binaryInfinitesimalDerivation_apply, binaryRotationBasis_infinitesimalRotation, smul_smul] at equality
  convert equality using 1
  congr 1
  congr 1
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
