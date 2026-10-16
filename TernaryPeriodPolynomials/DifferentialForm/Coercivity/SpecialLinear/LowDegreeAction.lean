module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowDegreeBasis
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.HodgeCasimir

@[expose] public section


/-! Verified real coordinate action of the compact generators in degrees one to three. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

theorem monomial_tripleExponent (a b c : ℕ) :
    monomial (tripleExponent a b c) (1 : ℝ) = X 0 ^ a * X 1 ^ b * X 2 ^ c := by
  simp only [tripleExponent, monomial_add_single, ← X_pow_eq_monomial]
  rfl

def lowCoefficientAction1 (k : Fin 3) (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![
  ![0, (-1 : ℝ) * x 2, x 1],
  ![(-1 : ℝ) * x 2, 0, x 0],
  ![(-1 : ℝ) * x 1, x 0, 0]] k

theorem lowCoefficientAction1_correct_0 (x : Fin 3 → ℝ) :
    infinitesimal (skewFrame (⟨0, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent1 x) =
      coordinatePolynomial lowExponent1 (lowCoefficientAction1 (⟨0, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent1,
    monomial_tripleExponent, lowCoefficientAction1, Fin.sum_univ_succ, smul_eq_C_mul]
  ring

theorem lowCoefficientAction1_correct_1 (x : Fin 3 → ℝ) :
    infinitesimal (skewFrame (⟨1, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent1 x) =
      coordinatePolynomial lowExponent1 (lowCoefficientAction1 (⟨1, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent1,
    monomial_tripleExponent, lowCoefficientAction1, Fin.sum_univ_succ, smul_eq_C_mul]
  ring

theorem lowCoefficientAction1_correct_2 (x : Fin 3 → ℝ) :
    infinitesimal (skewFrame (⟨2, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent1 x) =
      coordinatePolynomial lowExponent1 (lowCoefficientAction1 (⟨2, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent1,
    monomial_tripleExponent, lowCoefficientAction1, Fin.sum_univ_succ, smul_eq_C_mul]
  ring

theorem lowCoefficientAction1_correct (k : Fin 3) (x : Fin 3 → ℝ) :
    infinitesimal (skewFrame k) (coordinatePolynomial lowExponent1 x) =
      coordinatePolynomial lowExponent1 (lowCoefficientAction1 k x) := by
  fin_cases k
  · exact lowCoefficientAction1_correct_0 x
  · exact lowCoefficientAction1_correct_1 x
  · exact lowCoefficientAction1_correct_2 x

def lowCoefficientAction2 (k : Fin 3) (x : Fin 6 → ℝ) : Fin 6 → ℝ := ![
  ![0, (-1 : ℝ) * x 3, (-1 : ℝ) * x 4, x 1, (2 : ℝ) * x 2 + (-2 : ℝ) * x 5, x 4],
  ![(-1 : ℝ) * x 3, (-1 : ℝ) * x 4, 0, (2 : ℝ) * x 0 + (-2 : ℝ) * x 5, x 1, x 3],
  ![(-1 : ℝ) * x 1, (2 : ℝ) * x 0 + (-2 : ℝ) * x 2, x 1, (-1 : ℝ) * x 4, x 3, 0]] k

theorem lowCoefficientAction2_correct_0 (x : Fin 6 → ℝ) :
    infinitesimal (skewFrame (⟨0, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent2 x) =
      coordinatePolynomial lowExponent2 (lowCoefficientAction2 (⟨0, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent2,
    monomial_tripleExponent, lowCoefficientAction2, Fin.sum_univ_succ, smul_eq_C_mul]
  simp only [map_ofNat]
  ring

theorem lowCoefficientAction2_correct_1 (x : Fin 6 → ℝ) :
    infinitesimal (skewFrame (⟨1, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent2 x) =
      coordinatePolynomial lowExponent2 (lowCoefficientAction2 (⟨1, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent2,
    monomial_tripleExponent, lowCoefficientAction2, Fin.sum_univ_succ, smul_eq_C_mul]
  simp only [map_ofNat]
  ring

theorem lowCoefficientAction2_correct_2 (x : Fin 6 → ℝ) :
    infinitesimal (skewFrame (⟨2, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent2 x) =
      coordinatePolynomial lowExponent2 (lowCoefficientAction2 (⟨2, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent2,
    monomial_tripleExponent, lowCoefficientAction2, Fin.sum_univ_succ, smul_eq_C_mul]
  simp only [map_ofNat]
  ring

theorem lowCoefficientAction2_correct (k : Fin 3) (x : Fin 6 → ℝ) :
    infinitesimal (skewFrame k) (coordinatePolynomial lowExponent2 x) =
      coordinatePolynomial lowExponent2 (lowCoefficientAction2 k x) := by
  fin_cases k
  · exact lowCoefficientAction2_correct_0 x
  · exact lowCoefficientAction2_correct_1 x
  · exact lowCoefficientAction2_correct_2 x

def lowCoefficientAction3 (k : Fin 3) (x : Fin 10 → ℝ) : Fin 10 → ℝ := ![
  ![0, (-1 : ℝ) * x 4, (-1 : ℝ) * x 5, (-1 : ℝ) * x 6, x 1, (2 : ℝ) * x 2 + (-2 : ℝ) * x 7, (3 : ℝ) * x 3 + (-2 : ℝ) * x 8, x 5, (2 : ℝ) * x 6 + (-3 : ℝ) * x 9, x 8],
  ![(-1 : ℝ) * x 4, (-1 : ℝ) * x 5, (-1 : ℝ) * x 6, 0, (3 : ℝ) * x 0 + (-2 : ℝ) * x 7, (2 : ℝ) * x 1 + (-2 : ℝ) * x 8, x 2, (2 : ℝ) * x 4 + (-3 : ℝ) * x 9, x 5, x 7],
  ![(-1 : ℝ) * x 1, (3 : ℝ) * x 0 + (-2 : ℝ) * x 2, (2 : ℝ) * x 1 + (-3 : ℝ) * x 3, x 2, (-1 : ℝ) * x 5, (2 : ℝ) * x 4 + (-2 : ℝ) * x 6, x 5, (-1 : ℝ) * x 8, x 7, 0]] k

theorem lowCoefficientAction3_correct_0 (x : Fin 10 → ℝ) :
    infinitesimal (skewFrame (⟨0, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent3 x) =
      coordinatePolynomial lowExponent3 (lowCoefficientAction3 (⟨0, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent3,
    monomial_tripleExponent, lowCoefficientAction3, Fin.sum_univ_succ, smul_eq_C_mul]
  simp only [map_ofNat]
  ring

theorem lowCoefficientAction3_correct_1 (x : Fin 10 → ℝ) :
    infinitesimal (skewFrame (⟨1, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent3 x) =
      coordinatePolynomial lowExponent3 (lowCoefficientAction3 (⟨1, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent3,
    monomial_tripleExponent, lowCoefficientAction3, Fin.sum_univ_succ, smul_eq_C_mul]
  simp only [map_ofNat]
  ring

theorem lowCoefficientAction3_correct_2 (x : Fin 10 → ℝ) :
    infinitesimal (skewFrame (⟨2, by decide⟩ : Fin 3)) (coordinatePolynomial lowExponent3 x) =
      coordinatePolynomial lowExponent3 (lowCoefficientAction3 (⟨2, by decide⟩ : Fin 3) x) := by
  simp [infinitesimal_skewFrame, rotation, coordinatePolynomial, lowExponent3,
    monomial_tripleExponent, lowCoefficientAction3, Fin.sum_univ_succ, smul_eq_C_mul]
  simp only [map_ofNat]
  ring

theorem lowCoefficientAction3_correct (k : Fin 3) (x : Fin 10 → ℝ) :
    infinitesimal (skewFrame k) (coordinatePolynomial lowExponent3 x) =
      coordinatePolynomial lowExponent3 (lowCoefficientAction3 k x) := by
  fin_cases k
  · exact lowCoefficientAction3_correct_0 x
  · exact lowCoefficientAction3_correct_1 x
  · exact lowCoefficientAction3_correct_2 x

end TernaryPoly.SL3PolynomialCoercivity
