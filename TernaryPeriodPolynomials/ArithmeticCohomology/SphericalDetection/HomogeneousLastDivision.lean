module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperRadicalExponential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalCoinvariants
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def homogeneousLastMultiply (degree : ℕ) : HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly (degree + 1) where
  toFun polynomial := ⟨X 2 * polynomial.val, by
    change (X 2 * polynomial.val).IsHomogeneous (degree + 1)
    simpa only [Nat.add_comm] using (isHomogeneous_X ℂ (2 : Fin 3)).mul polynomial.property⟩
  map_add' first second := Subtype.ext (mul_add _ _ _)
  map_smul' scalar polynomial := Subtype.ext (mul_smul_comm _ _ _)

theorem homogeneousLastMultiply_injective (degree : ℕ) : Function.Injective (homogeneousLastMultiply degree) := by
  intro first second equality
  apply Subtype.ext
  exact (X_mul_cancel_left_iff).mp (congrArg Subtype.val equality)

def homogeneousLastDivide (degree : ℕ) : HomogeneousPoly (degree + 1) →ₗ[ℂ] HomogeneousPoly degree where
  toFun polynomial := ⟨polynomial.val.divMonomial (Finsupp.single 2 1), by
    intro exponent nonzero
    have shifted : polynomial.val.coeff (Finsupp.single 2 1 + exponent) ≠ 0 := by
      simpa only [coeff_divMonomial] using nonzero
    have degree_eq := polynomial.property shifted
    have degree_eq' : (Finsupp.single 2 1 + exponent).degree = degree + 1 := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using degree_eq
    have sum_eq : 1 + exponent.degree = degree + 1 := by
      simpa only [map_add, Finsupp.degree_single] using degree_eq'
    have result : exponent.degree = degree := by omega
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using result⟩
  map_add' first second := Subtype.ext (add_divMonomial _ _ _)
  map_smul' scalar polynomial := by
    apply Subtype.ext
    change (scalar • polynomial.val).divMonomial (Finsupp.single 2 1) =
      scalar • polynomial.val.divMonomial (Finsupp.single 2 1)
    ext exponent
    simp only [coeff_divMonomial, coeff_smul]

theorem homogeneousLastDivide_multiply (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    homogeneousLastDivide degree (homogeneousLastMultiply degree polynomial) = polynomial := by
  apply Subtype.ext
  exact X_mul_divMonomial 2 polynomial.val

theorem homogeneousLastMultiply_divide (degree : ℕ) (polynomial : HomogeneousPoly (degree + 1))
    (zero : binaryHomogeneousRestrict (degree + 1) polynomial = 0) :
    homogeneousLastMultiply degree (homogeneousLastDivide degree polynomial) = polynomial := by
  have restricted : binaryPolynomialRestrict polynomial.val = 0 := congrArg Subtype.val zero
  obtain ⟨factor, equality⟩ := (binaryPolynomialRestrict_zero_iff_dvd polynomial.val).mp restricted
  apply Subtype.ext
  change X 2 * polynomial.val.divMonomial (Finsupp.single 2 1) = polynomial.val
  rw [equality, X_mul_divMonomial]

theorem polynomialUpperAction_last_mul (first second : ℂ) (polynomial : Poly) :
    action (-1) (planeUnipotent first second) (X 2 * polynomial) =
      X 2 * action (-1) (planeUnipotent first second) polynomial := by
  have last : substitute (planeUnipotent first second)⁻¹.val (X 2) = X 2 := by
    simp [substitute_X, linearForm, planeUnipotent, Fin.sum_univ_three]
  rw [action_apply, map_mul, last, action_apply, mul_smul_comm]

theorem homogeneousLastMultiply_realUpper (degree : ℕ) (element : RealPlaneRadical)
    (polynomial : HomogeneousPoly degree) :
    homogeneousLastMultiply degree ((realUpperRadicalRep degree).ρ element polynomial) =
      (realUpperRadicalRep (degree + 1)).ρ element (homogeneousLastMultiply degree polynomial) := by
  change homogeneousLastMultiply degree (realCoefficientComponent degree trivialCharacter
      (planeUnipotent (element.toAdd 0) (element.toAdd 1)) polynomial) =
    realCoefficientComponent (degree + 1) trivialCharacter
      (planeUnipotent (element.toAdd 0) (element.toAdd 1)) (homogeneousLastMultiply degree polynomial)
  rw [realCoefficientComponent_trivial, realCoefficientComponent_trivial, map_planeUnipotent]
  apply Subtype.ext
  exact (polynomialUpperAction_last_mul _ _ polynomial.val).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
