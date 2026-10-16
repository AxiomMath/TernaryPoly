module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalBernoulli
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def firstAntiderivative (p : Poly) : Poly :=
  ∑ exponent ∈ p.support, monomial (exponent + Finsupp.single 0 1)
    (p.coeff exponent / ((exponent 0 : ℂ) + 1))

theorem firstAntiderivative_pderiv (p : Poly) : pderiv 0 (firstAntiderivative p) = p := by
  classical
  rw [firstAntiderivative, map_sum]
  conv_rhs => rw [← support_sum_monomial_coeff p]
  apply Finset.sum_congr rfl
  intro exponent _
  have nonzero : (exponent 0 : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (exponent 0)
  rw [pderiv_monomial]
  simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.cast_add, Nat.cast_one, div_mul_cancel₀ _ nonzero]

theorem firstAntiderivative_homogeneous {n : ℕ} (p : Poly)
    (homogeneous : p.IsHomogeneous n) : (firstAntiderivative p).IsHomogeneous (n+1) := by
  classical
  apply IsHomogeneous.sum
  intro exponent supported
  apply isHomogeneous_monomial
  have degree_eq := homogeneous (mem_support_iff.mp supported)
  rw [map_add, Finsupp.degree_single]
  have degree_eq' : Finsupp.degree exponent = n := by
    simpa only [Finsupp.weight_apply, Finsupp.degree_apply, Pi.one_apply,
      smul_eq_mul, mul_one, Finsupp.sum] using degree_eq
  rw [degree_eq']

theorem homogeneous_of_X_mul {n : ℕ} (p : Poly) (i : Fin 3)
    (homogeneous : (X i * p).IsHomogeneous n) : p.IsHomogeneous (n-1) := by
  intro exponent nonzero
  have supported : (X i * p).coeff (Finsupp.single i 1 + exponent) ≠ 0 := by
    rwa [coeff_X_mul]
  have degree_eq := homogeneous supported
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, one_smul] at degree_eq
  omega

theorem bernoulliOperator_homogeneous (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) : (bernoulliOperator n t p.val).IsHomogeneous n := by
  rw [bernoulliOperator_eq_endomorphism n positive t linear independent p]
  exact ((∑ k ∈ Finset.range (n+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) •
    (polynomialTranslationDerivative n positive t linear)^k) p).property

theorem radical_primitive_of_bernoulli_zero (n : ℕ) (positive : 0 < n)
    (first second : HomogeneousPoly n)
    (zero_coordinate : X 2 * bernoulliOperator n (X 1) first.val -
      X 1 * bernoulliOperator n (X 2) second.val = 0) :
    ∃ primitive : HomogeneousPoly n,
      first = primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 1 0) primitive ∧
      second = primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 0 1) primitive := by
  let alpha := bernoulliOperator n (X 1) first.val
  let beta := bernoulliOperator n (X 2) second.val
  have relation : X 2 * alpha = X 1 * beta := sub_eq_zero.mp zero_coordinate
  have divides : X 1 ∣ X 2 * alpha := by
    rw [relation]
    exact dvd_mul_right _ _
  have coprime : ¬ (X (1 : Fin 3) : Poly) ∣ X 2 := by
    rw [X_dvd_X]
    decide
  obtain ⟨h, alpha_eq⟩ := (X_dvd_mul_iff.mp divides).resolve_left coprime
  have beta_eq : beta = X 2 * h := by
    apply mul_left_cancel₀ (X_ne_zero (1 : Fin 3))
    rw [← relation, alpha_eq]
    ring
  have homogeneous_h : h.IsHomogeneous (n-1) := by
    apply homogeneous_of_X_mul h 1
    rw [← alpha_eq]
    exact bernoulliOperator_homogeneous n positive (X 1) (isHomogeneous_X ℂ 1)
      (by simp) first
  let primitive : HomogeneousPoly n := ⟨firstAntiderivative h, by
    change (firstAntiderivative h).IsHomogeneous n
    have degree_eq : n-1+1 = n := Nat.sub_add_cancel positive
    simpa only [degree_eq] using firstAntiderivative_homogeneous h homogeneous_h⟩
  have derivative : pderiv 0 primitive.val = h := firstAntiderivative_pderiv h
  refine ⟨primitive, ?_, ?_⟩
  · apply bernoulliOperator_injective n positive (X 1) (isHomogeneous_X ℂ 1) (by simp)
    change alpha = bernoulliOperator n (X 1)
      (primitive.val - (rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 1 0) primitive).val)
    rw [rationalCoefficient_lineUnipotent]
    simp only [Rat.cast_one, Rat.cast_zero, map_one, map_zero, one_mul, zero_mul,
      sub_zero, evalTriple, aeval_eq_bind₁]
    rw [bernoulliOperator_coboundary n positive (X 1) (isHomogeneous_X ℂ 1)
      (by simp) primitive, derivative, alpha_eq]
  · apply bernoulliOperator_injective n positive (X 2) (isHomogeneous_X ℂ 2) (by simp)
    change beta = bernoulliOperator n (X 2)
      (primitive.val - (rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent 0 1) primitive).val)
    rw [rationalCoefficient_lineUnipotent]
    simp only [Rat.cast_one, Rat.cast_zero, map_one, map_zero, one_mul, zero_mul,
      sub_zero, evalTriple, aeval_eq_bind₁]
    rw [bernoulliOperator_coboundary n positive (X 2) (isHomogeneous_X ℂ 2)
      (by simp) primitive, derivative, beta_eq]

theorem mixed_primitive_on_generators_of_coordinate_zero (n : ℕ) (positive : 0 < n)
    (c : Homogeneous.cocycles rationalLevel
      (rationalCoefficientComponent n trivialCharacter)) (levi : RationalGL3)
    (coordinate_zero : mixedBernoulliCoordinate c levi = 0) :
    ∃ primitive : HomogeneousPoly n,
      ∀ i : Fin 2,
        mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi
          (![Adelic.lineUnipotent 1 0, Adelic.lineUnipotent 0 1] i) =
        primitive - rationalCoefficientComponent n trivialCharacter
          (![Adelic.lineUnipotent 1 0, Adelic.lineUnipotent 0 1] i) primitive := by
  obtain ⟨primitive, first_eq, second_eq⟩ := radical_primitive_of_bernoulli_zero n positive
    (mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi
      (Adelic.lineUnipotent 1 0))
    (mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi
      (Adelic.lineUnipotent 0 1)) (by
        simpa only [mixedValue_eq_mixedBarEdge, mixedBernoulliCoordinate] using coordinate_zero)
  refine ⟨primitive, ?_⟩
  intro i
  fin_cases i
  · exact first_eq
  · exact second_eq

theorem normalizedBadLine_reflection_primitives (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n)
    (c : Homogeneous.cocycles rationalLevel
      (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    ∀ reflection ∈ ({binaryB, binaryR} : Set RationalGL3),
      ∃ primitive : HomogeneousPoly n, ∀ i : Fin 2,
        mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c reflection
          (![Adelic.lineUnipotent 1 0, Adelic.lineUnipotent 0 1] i) =
        primitive - rationalCoefficientComponent n trivialCharacter
          (![Adelic.lineUnipotent 1 0, Adelic.lineUnipotent 0 1] i) primitive := by
  intro reflection selected
  apply mixed_primitive_on_generators_of_coordinate_zero n positive c reflection
  rcases selected with rfl | rfl
  · exact normalized.2.2.1
  · exact normalized.2.2.2

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
