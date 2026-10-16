module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BinaryAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def radicalPairCoordinate (n : ℕ) (first second : HomogeneousPoly n) : Poly :=
  X 2 * bernoulliOperator n (X 1) first.val - X 1 * bernoulliOperator n (X 2) second.val

theorem radicalPairCoordinate_add (n : ℕ) (first second first' second' : HomogeneousPoly n) :
    radicalPairCoordinate n (first+first') (second+second') =
      radicalPairCoordinate n first second + radicalPairCoordinate n first' second' := by
  simp only [radicalPairCoordinate, Submodule.coe_add, bernoulliOperator_add]
  ring

theorem mixedBernoulliCoordinate_eq_pair (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (levi : RationalGL3) :
    mixedBernoulliCoordinate c levi = radicalPairCoordinate n
      (mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi
        (Adelic.lineUnipotent 1 0))
      (mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi
        (Adelic.lineUnipotent 0 1)) := by
  simp only [radicalPairCoordinate, mixedValue_eq_mixedBarEdge, mixedBernoulliCoordinate]

theorem mixedBernoulliCoordinate_A_mul (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (levi : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      levi.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * levi.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ))
    (pure_product : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryA levi.val = 0) :
    mixedBernoulliCoordinate c (binaryA * levi.val) = mixedBernoulliCoordinate c binaryA +
      binaryASubstitution (mixedBernoulliCoordinate c levi.val) := by
  let values := fun x : ℤ × ℤ => mixedValue rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c levi.val
      (integralRadicalHom (Multiplicative.ofAdd x))
  have covariance := radicalCoordinate_binaryA n positive values
    (mixedValue_integralRadical_cocycle n c pure levi normalizes)
  have first := mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c ⟨binaryA,binaryA_mem⟩
    ⟨Adelic.lineUnipotent 1 0, by simpa using rationalLevel_lineUnipotent 1 0⟩
    levi.val pure_product
  have second := mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c ⟨binaryA,binaryA_mem⟩
    ⟨Adelic.lineUnipotent 0 1, by simpa using rationalLevel_lineUnipotent 0 1⟩
    levi.val pure_product
  simp only [binaryA_conjugate, mul_zero, mul_one, add_zero, zero_add, neg_zero,
    sub_zero, zero_sub] at first second
  simp only [mixedBernoulliCoordinate_eq_pair]
  rw [first, second, radicalPairCoordinate_add]
  congr 1

theorem badLineLevi_mul (first second : IntegralGL3)
    (first_mem : BadLineLevi first) (second_mem : BadLineLevi second) :
    BadLineLevi (first*second) := by
  rcases first_mem with ⟨first_level,h₁,h₂,h₃,h₄⟩
  rcases second_mem with ⟨second_level,k₁,k₂,k₃,k₄⟩
  refine ⟨arithmeticLevel.mul_mem first_level second_level, ?_, ?_, ?_, ?_⟩ <;>
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      h₁,h₂,h₃,h₄,k₁,k₂,k₃,k₄, zero_mul, mul_zero, add_zero]

theorem radical_normalizes_mul (first second : RationalGL3)
    (first_normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      first⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * first =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ))
    (second_normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      second⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * second =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ)) (s t : ℤ) : ∃ s' t' : ℤ,
    (first*second)⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * (first*second) =
      Adelic.lineUnipotent (s' : ℚ) (t' : ℚ) := by
  obtain ⟨a,b,first_eq⟩ := first_normalizes s t
  obtain ⟨a',b',second_eq⟩ := second_normalizes a b
  refine ⟨a',b',?_⟩
  rw [_root_.mul_inv_rev]
  calc
    _ = second⁻¹ * (first⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * first) * second := by
      group
    _ = _ := by rw [first_eq,second_eq]

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
