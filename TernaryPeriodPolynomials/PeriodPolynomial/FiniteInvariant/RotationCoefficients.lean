module

public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Coordinates
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.BinomialTrace
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryExtremeSmallDegree
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.BinomialCoefficient

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant
open BinaryHomogeneous

/-- The unsigned coefficient beneath the actual order-three substitution. -/
theorem coeff_monomial_add_pow (d : ℕ) (i : Fin (d+1)) :
    ((X 1)^i.val*(X 0+X 1 : MvPolynomial (Fin 2) ℚ)^(d-i.val)).coeff (exponent d i) =
      ((d-i.val).choose i.val : ℚ) := by
  exact coeff_Y_mul_add_pow i.val (d-i.val)

/-- The rotation diagonal entries are literal signed binomial coefficients. -/
theorem rotation_diagonal (d : ℕ) (i : Fin (d+1)) :
    coordinates ℚ d (rotation d (monomialVector d i)) i =
      (-1 : ℚ)^(d-i.val) * ((d-i.val).choose i.val : ℚ) := by
  change (rotation d (monomialVector d i)).val.coeff (exponent d i) = _
  rw [rotation_coe,monomialVector_powers]
  have he : bind₁ (![-X 1,X 0-X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)
        ((X 0)^i.val*(X 1)^(d-i.val)) =
      bind₁ ![C (1 : ℚ)*X 0,C (-1 : ℚ)*X 1]
        ((X 1)^i.val*(X 0+X 1)^(d-i.val)) := by
    simp [sub_eq_add_neg]
  rw [he,BinaryExtreme.coeff_diagonal,exponent_zero,exponent_one,one_pow,one_mul,
    coeff_monomial_add_pow]

/-- In even homogeneous degree the diagonal sign is the first-coordinate parity. -/
theorem rotation_diagonal_even (d : ℕ) (hd : Even d) (i : Fin (d+1)) :
    coordinates ℚ d (rotation d (monomialVector d i)) i =
      (-1 : ℚ)^i.val * ((d-i.val).choose i.val : ℚ) := by
  rw [rotation_diagonal,neg_one_pow_eq_pow_mod_two (d-i.val),neg_one_pow_eq_pow_mod_two i.val]
  congr 2
  rw [Nat.even_iff] at hd
  have hi := i.isLt
  omega

/-- Trace of the order-three operator as one uniform rational binomial sum. -/
theorem trace_rotation_sum (d : ℕ) (hd : Even d) :
    LinearMap.trace ℚ (H d) (rotation d)=rotationSum d := by
  rw [trace_coordinates]
  simp_rw [rotation_diagonal_even d hd]
  exact Fin.sum_univ_eq_sum_range (fun i => (-1 : ℚ)^i*((d-i).choose i : ℚ)) (d+1)

end TernaryPoly.BinaryFiniteInvariant
