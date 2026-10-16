module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialDerivativeKernel

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryPolynomialRestrict : Poly →ₐ[ℂ] Binary.Poly := bind₁ ![X 0, X 1, 0]

theorem binaryPolynomialRestrict_lift (polynomial : Binary.Poly) :
    binaryPolynomialRestrict (binaryPolynomialLift polynomial) = polynomial := by
  have identity : binaryPolynomialRestrict.comp binaryPolynomialLift = AlgHom.id ℂ Binary.Poly := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [binaryPolynomialRestrict, binaryPolynomialLift]
  exact congrArg (fun hom : Binary.Poly →ₐ[ℂ] Binary.Poly => hom polynomial) identity

theorem binaryPolynomialRestrict_X (index : Fin 3) :
    binaryPolynomialRestrict (X index) = (![X 0, X 1, 0] : Fin 3 → Binary.Poly) index := by
  simp [binaryPolynomialRestrict]

theorem binaryPolynomialRestrict_homogeneous {degree : ℕ} (polynomial : Poly)
    (homogeneous : polynomial.IsHomogeneous degree) :
    (binaryPolynomialRestrict polynomial).IsHomogeneous degree := by
  have coordinates : ∀ index : Fin 3, ((![X 0, X 1, 0] : Fin 3 → Binary.Poly) index).IsHomogeneous 1 := by
    intro index
    fin_cases index
    · exact isHomogeneous_X ℂ (0 : Fin 2)
    · exact isHomogeneous_X ℂ (1 : Fin 2)
    · exact isHomogeneous_zero (Fin 2) ℂ 1
  have result := homogeneous.aeval (![X 0, X 1, 0] : Fin 3 → Binary.Poly) coordinates
  change ((bind₁ ![X 0, X 1, 0]) polynomial).IsHomogeneous degree
  simpa only [one_mul, aeval_eq_bind₁] using result

theorem binaryPolynomialRestrict_difference_dvd (polynomial : Poly) :
    (X (2 : Fin 3) : Poly) ∣ polynomial - binaryPolynomialLift (binaryPolynomialRestrict polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [binaryPolynomialRestrict, binaryPolynomialLift]
  | add first second first_divides second_divides =>
    rw [map_add, map_add]
    convert dvd_add first_divides second_divides using 1
    ring
  | mul_X polynomial index divides =>
    rw [map_mul, map_mul, binaryPolynomialRestrict_X]
    fin_cases index
    · change X 2 ∣ polynomial * X 0 - binaryPolynomialLift (binaryPolynomialRestrict polynomial) *
        binaryPolynomialLift (X 0)
      have lift : binaryPolynomialLift (X (0 : Fin 2)) = X (0 : Fin 3) := by simp [binaryPolynomialLift]
      rw [lift]
      convert dvd_mul_of_dvd_left divides (X (0 : Fin 3)) using 1
      ring
    · change X 2 ∣ polynomial * X 1 - binaryPolynomialLift (binaryPolynomialRestrict polynomial) *
        binaryPolynomialLift (X 1)
      have lift : binaryPolynomialLift (X (1 : Fin 2)) = X (1 : Fin 3) := by simp [binaryPolynomialLift]
      rw [lift]
      convert dvd_mul_of_dvd_left divides (X (1 : Fin 3)) using 1
      ring
    · change X 2 ∣ polynomial * X 2 - binaryPolynomialLift (binaryPolynomialRestrict polynomial) *
        binaryPolynomialLift 0
      rw [map_zero, mul_zero, sub_zero]
      exact dvd_mul_left (X 2) polynomial

theorem binaryPolynomialRestrict_zero_iff_dvd (polynomial : Poly) :
    binaryPolynomialRestrict polynomial = 0 ↔ (X (2 : Fin 3) : Poly) ∣ polynomial := by
  constructor
  · intro zero
    have divides := binaryPolynomialRestrict_difference_dvd polynomial
    rwa [zero, map_zero, sub_zero] at divides
  · rintro ⟨factor, rfl⟩
    rw [map_mul, binaryPolynomialRestrict_X]
    simp

theorem binaryPolynomialRestrict_pderiv (index : Fin 2) (polynomial : Poly) :
    pderiv index (binaryPolynomialRestrict polynomial) =
      binaryPolynomialRestrict (pderiv index.castSucc polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [binaryPolynomialRestrict]
  | add first second first_eq second_eq =>
    rw [map_add, map_add, map_add, map_add, first_eq, second_eq]
  | mul_X polynomial generator equality =>
    rw [map_mul, pderiv_mul, pderiv_mul, map_add, map_mul, map_mul, equality]
    congr 1
    congr 1
    fin_cases index <;> fin_cases generator <;>
      simp [binaryPolynomialRestrict, pderiv_X]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
