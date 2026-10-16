module

public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.Covariance
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Operators

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.BinaryApolar
open BinaryFiniteInvariant

/-- The finite-group matrix operator is exactly the substitution used in apolar covariance. -/
theorem operator_eq_transform (d : ℕ) (M : Mat) :
    operator d M=transform ℚ d (M 0 0) (M 0 1) (M 1 0) (M 1 1) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change bind₁ (BinaryModularSymbolCoefficients.linearForm M) p.val = bind₁ _ p.val
  congr 2
  funext i
  fin_cases i <;> simp [BinaryModularSymbolCoefficients.linearForm,Fin.sum_univ_two]

/-- Swap preserves the actual apolar form in even degree. -/
theorem swap_isometry (d : ℕ) (hd : Even d) (p q : H d) :
    form ℚ d (swap d p) (swap d q)=form ℚ d p q := by
  rw [swap,operator_eq_transform]
  change form ℚ d (transform ℚ d 0 1 1 0 p) (transform ℚ d 0 1 1 0 q)=_
  simpa only [zero_mul,one_mul,zero_sub,hd.neg_one_pow] using covariance ℚ d 0 1 1 0 p q

/-- First-coordinate reflection preserves the actual apolar form in even degree. -/
theorem negateFirst_isometry (d : ℕ) (hd : Even d) (p q : H d) :
    form ℚ d (negateFirst d p) (negateFirst d q)=form ℚ d p q := by
  rw [negateFirst,operator_eq_transform]
  change form ℚ d (transform ℚ d (-1) 0 0 1 p) (transform ℚ d (-1) 0 0 1 q)=_
  simpa only [mul_one,zero_mul,sub_zero,hd.neg_one_pow,one_mul] using covariance ℚ d (-1) 0 0 1 p q

/-- The order-three substitution has determinant one and preserves apolarity in every degree. -/
theorem rotation_isometry (d : ℕ) (p q : H d) :
    form ℚ d (rotation d p) (rotation d q)=form ℚ d p q := by
  rw [rotation,operator_eq_transform]
  change form ℚ d (transform ℚ d 0 (-1) 1 (-1) p) (transform ℚ d 0 (-1) 1 (-1) q)=_
  simpa only [zero_mul,mul_one,zero_sub,neg_neg,one_pow,one_mul] using covariance ℚ d 0 (-1) 1 (-1) p q

/-- Involutive isometries are self-adjoint for the actual bilinear pairing. -/
theorem swap_adjoint (d : ℕ) (hd : Even d) (p q : H d) :
    form ℚ d (swap d p) q=form ℚ d p (swap d q) := by
  have h := swap_isometry d hd p (swap d q)
  rw [show swap d (swap d q)=q from LinearMap.congr_fun (swap_sq d) q] at h
  exact h

theorem negateFirst_adjoint (d : ℕ) (hd : Even d) (p q : H d) :
    form ℚ d (negateFirst d p) q=form ℚ d p (negateFirst d q) := by
  have h := negateFirst_isometry d hd p (negateFirst d q)
  rw [show negateFirst d (negateFirst d q)=q from LinearMap.congr_fun (negateFirst_sq d) q] at h
  exact h

/-- The adjoint of rotation is its square. -/
theorem rotation_adjoint (d : ℕ) (p q : H d) :
    form ℚ d (rotation d p) q=form ℚ d p (rotation d (rotation d q)) := by
  have h := rotation_isometry d p (rotation d (rotation d q))
  rw [show rotation d (rotation d (rotation d q))=q from
    LinearMap.congr_fun (rotation_cube d) q] at h
  exact h

end TernaryPoly.BinaryApolar
