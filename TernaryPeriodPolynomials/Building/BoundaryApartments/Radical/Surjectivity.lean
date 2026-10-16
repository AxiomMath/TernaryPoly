module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.BoundaryDetection

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous MvPolynomial

theorem binaryProjection_pderiv_nonzero (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : Poly) :
    pderiv index (binaryProjection polynomial) = binaryProjection (pderiv index polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp [binaryProjection]
  | add first second first_eq second_eq => simp only [map_add, first_eq, second_eq]
  | mul_X polynomial current induction_hypothesis =>
    rw [map_mul, pderiv_mul, induction_hypothesis, pderiv_mul, map_add, map_mul, map_mul]
    have variable_eq : pderiv index (binaryProjection (X current)) =
        binaryProjection (pderiv index (X current)) := by
      fin_cases current
      · simp [binaryProjection, index_nonzero]
      · by_cases index_one : index = 1
        · subst index
          simp [binaryProjection]
        · simp [binaryProjection, pderiv_X_of_ne (Ne.symm index_one)]
      · by_cases index_two : index = 2
        · subst index
          simp [binaryProjection]
        · simp [binaryProjection, pderiv_X_of_ne (Ne.symm index_two)]
    rw [variable_eq]

theorem pderiv_binary_nonzero (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : Poly) (binary : pderiv 0 polynomial = 0) :
    pderiv 0 (pderiv index polynomial) = 0 := by
  have projected : binaryProjection (pderiv index polynomial) = pderiv index polynomial := by
    rw [← binaryProjection_pderiv_nonzero index index_nonzero,
      binaryProjection_eq_self polynomial binary]
  rw [← projected]
  exact binaryProjection_pderiv _

theorem radicalCoordinate_binary_surjective (degree : ℕ)
    (polynomial : HomogeneousPoly (degree + 1)) (binary : pderiv 0 polynomial.val = 0) :
    ∃ first second : HomogeneousPoly degree,
      pderiv 0 first.val = 0 ∧ pderiv 0 second.val = 0 ∧
      radicalContractionMap degree (first, second) = polynomial.val := by
  let coefficient : ℂ := ((degree + 1 : ℕ) : ℂ)⁻¹
  let first : HomogeneousPoly degree :=
    ⟨C coefficient * pderiv 2 polynomial.val,
      by change (C coefficient * pderiv 2 polynomial.val).IsHomogeneous degree
         simpa only [Nat.add_sub_cancel] using
        (polynomial.property.pderiv (i := (2 : Fin 3))).C_mul coefficient⟩
  let second : HomogeneousPoly degree :=
    ⟨C (-coefficient) * pderiv 1 polynomial.val,
      by change (C (-coefficient) * pderiv 1 polynomial.val).IsHomogeneous degree
         simpa only [Nat.add_sub_cancel] using
        (polynomial.property.pderiv (i := (1 : Fin 3))).C_mul (-coefficient)⟩
  have first_binary : pderiv 0 first.val = 0 := by
    change pderiv 0 (C coefficient * pderiv 2 polynomial.val) = 0
    rw [pderiv_C_mul, pderiv_binary_nonzero 2 (by decide) polynomial.val binary, mul_zero]
  have second_binary : pderiv 0 second.val = 0 := by
    change pderiv 0 (C (-coefficient) * pderiv 1 polynomial.val) = 0
    rw [pderiv_C_mul, pderiv_binary_nonzero 1 (by decide) polynomial.val binary, mul_zero]
  refine ⟨first, second, first_binary, second_binary, ?_⟩
  rw [radicalContractionMap_binary degree first second first_binary second_binary]
  have euler := polynomial.property.sum_X_mul_pderiv
  rw [Fin.sum_univ_three, binary, mul_zero, zero_add] at euler
  have degree_nonzero : (((degree + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero degree
  change X 2 * (C coefficient * pderiv 2 polynomial.val) -
    X 1 * (C (-coefficient) * pderiv 1 polynomial.val) = polynomial.val
  rw [show X 2 * (C coefficient * pderiv 2 polynomial.val) -
      X 1 * (C (-coefficient) * pderiv 1 polynomial.val) =
      C coefficient * (X 1 * pderiv 1 polynomial.val + X 2 * pderiv 2 polynomial.val) by
        rw [map_neg]; ring, euler]
  have scalar : (degree + 1) • polynomial.val = C (((degree + 1 : ℕ) : ℂ)) * polynomial.val := by
    simp only [nsmul_eq_mul, map_natCast]
  rw [scalar, ← mul_assoc, ← map_mul]
  rw [show coefficient * (((degree + 1 : ℕ) : ℂ)) = 1 from inv_mul_cancel₀ degree_nonzero]
  simp

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
