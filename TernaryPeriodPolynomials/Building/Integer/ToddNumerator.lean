module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd.IntegralCongruences
public import TernaryPeriodPolynomials.AlternatingSolution.Todd
public import TernaryPeriodPolynomials.Building.Primitive.Transfer
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.IntegerToddNumerator
open ToddIntegralCongruences BernoulliTwoIntegral

/-- The first integer frame of the actual alternating Todd expression. -/
def integerFrame1 (f : MvPolynomial (Fin 3) ℤ) : MvPolynomial (Fin 3) ℤ :=
  bind₁ ![X 2 - 2*X 1, -X 0, X 0-X 1] f

/-- The second integer frame, with all three signs positive. -/
def integerFrame2 (f : MvPolynomial (Fin 3) ℤ) : MvPolynomial (Fin 3) ℤ :=
  integerFrame1 f + bind₁ ![X 2-X 0, X 0-2*X 1, -X 1] f +
    bind₁ ![X 2-2*X 1, X 1-X 0, X 0-2*X 1] f

/-- The literal integer numerator obtained by replacing four times Todd by B₄. -/
def integerN4 (f : MvPolynomial (Fin 3) ℤ) : MvPolynomial (Fin 3) ℤ :=
  (finSuccEquiv ℤ 2).symm
    ((X 1 : MvPolynomial (Fin 2) ℤ) •
        b4Operator (X 0) (finSuccEquiv ℤ 2 (integerFrame1 f)) -
      (X 0 : MvPolynomial (Fin 2) ℤ) •
        b4Operator (X 1) (finSuccEquiv ℤ 2 (integerFrame2 f)))

theorem integerFrame1_map (f : MvPolynomial (Fin 3) ℤ) :
    integerCoefficientMap (integerFrame1 f) = alternatingFrame1 (integerCoefficientMap f) := by
  simp [integerFrame1, alternatingFrame1, substitute3, integerCoefficientMap,
    PrimitiveTransfer.map_bind_vec3]

theorem integerFrame2_map (f : MvPolynomial (Fin 3) ℤ) :
    integerCoefficientMap (integerFrame2 f) = alternatingFrame2 (integerCoefficientMap f) := by
  simp only [integerFrame2, map_add, integerFrame1_map, alternatingFrame2,
    substitute3, integerCoefficientMap, PrimitiveTransfer.map_bind_vec3,
    map_sub, map_X, map_mul, map_ofNat, map_neg]

/-- Changing coefficient rings commutes with separating the first variable. -/
theorem finSuccEquiv_integer_map {n : ℕ} (f : MvPolynomial (Fin (n+1)) ℤ) :
    finSuccEquiv ℚ n (integerCoefficientMap f) =
      integerPolynomialMap (finSuccEquiv ℤ n f) := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro d
  simp only [finSuccEquiv_coeff_coeff, integerPolynomialMap, Polynomial.coeff_map,
    integerCoefficientMap, MvPolynomial.coeff_map]

/-- An odd denominator cannot remove divisibility of an integer by eight. -/
theorem eight_dvd_int_of_twoIntegral {n : ℤ} {q : ℚ}
    (h : (n : ℚ) = 8*q) (hq : TwoIntegral q) : (8 : ℤ) ∣ n := by
  have he : n * (q.den : ℤ) = 8*q.num := by
    have heq : (n : ℚ) * q.den = 8*q.num := by
      rw [h, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast heq
  have ho : Odd (q.den : ℤ) := by exact_mod_cast hq
  obtain ⟨k, hk⟩ := ho
  have hc₂ : IsCoprime (2 : ℤ) (q.den : ℤ) := ⟨-k, 1, by omega⟩
  have hc : IsCoprime (8 : ℤ) (q.den : ℤ) := by
    convert hc₂.pow_left (m := 3) using 1
    norm_num
  exact hc.dvd_of_dvd_mul_right ⟨q.num, he⟩

lemma coeffTwoIntegral_sub {σ : Type*} {p q : Polynomial (MvPolynomial σ ℚ)}
    (hp : CoeffTwoIntegral p) (hq : CoeffTwoIntegral q) : CoeffTwoIntegral (p-q) := by
  intro n d
  simpa only [Polynomial.coeff_sub, MvPolynomial.coeff_sub] using (hp n d).sub (hq n d)

lemma coeffTwoIntegral_X_smul {σ : Type*} (i : σ)
    {p : Polynomial (MvPolynomial σ ℚ)} (hp : CoeffTwoIntegral p) :
    CoeffTwoIntegral ((X i : MvPolynomial σ ℚ) • p) := by
  classical
  intro n d
  rw [Polynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_X_mul']
  split_ifs
  · exact hp n _
  · exact twoIntegral_zero

/-- Coefficientwise descent of an odd-denominator rational quotient. -/
theorem eight_dvd_polynomial_of_remainder {σ : Type*}
    (p : Polynomial (MvPolynomial σ ℤ)) (q : Polynomial (MvPolynomial σ ℚ))
    (hq : CoeffTwoIntegral q)
    (h : integerPolynomialMap p = (8 : MvPolynomial σ ℚ) • q) :
    (8 : Polynomial (MvPolynomial σ ℤ)) ∣ p := by
  rw [← Polynomial.C_ofNat, Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  change MvPolynomial.C (8 : ℤ) ∣ p.coeff n
  rw [MvPolynomial.C_dvd_iff_dvd_coeff]
  intro d
  apply eight_dvd_int_of_twoIntegral (q := (q.coeff n).coeff d) _ (hq n d)
  have he := congrArg (fun r : Polynomial (MvPolynomial σ ℚ) => (r.coeff n).coeff d) h
  simpa [integerPolynomialMap, integerCoefficientMap, Polynomial.coeff_smul,
    MvPolynomial.coeff_map, smul_eq_mul,
    show (8 : MvPolynomial σ ℚ) = MvPolynomial.C (8 : ℚ) from rfl,
    MvPolynomial.coeff_C_mul] using he

/-- The actual Todd-zero relation forces the integer B₄ numerator to vanish modulo eight. -/
theorem integerN4_dvd_eight (f : MvPolynomial (Fin 3) ℤ)
    (hzero : alternatingTodd (integerCoefficientMap f) = 0) :
    (8 : MvPolynomial (Fin 3) ℤ) ∣ integerN4 f := by
  let p₁ := finSuccEquiv ℤ 2 (integerFrame1 f)
  let p₂ := finSuccEquiv ℤ 2 (integerFrame2 f)
  obtain ⟨q₁, hq₁, h₁⟩ := todd_b4_integral_remainder (X (0 : Fin 2)) p₁
  obtain ⟨q₂, hq₂, h₂⟩ := todd_b4_integral_remainder (X (1 : Fin 2)) p₂
  have hz := congrArg (finSuccEquiv ℚ 2) hzero
  rw [finSuccEquiv_alternatingTodd, map_zero, ← integerFrame1_map,
    ← integerFrame2_map, finSuccEquiv_integer_map, finSuccEquiv_integer_map] at hz
  change (X 1 : MvPolynomial (Fin 2) ℚ) • todd (X 0) (integerPolynomialMap p₁) -
    (X 0 : MvPolynomial (Fin 2) ℚ) • todd (X 1) (integerPolynomialMap p₂) = 0 at hz
  have he : integerPolynomialMap
      ((X 1 : MvPolynomial (Fin 2) ℤ) • b4Operator (X 0) p₁ -
        (X 0 : MvPolynomial (Fin 2) ℤ) • b4Operator (X 1) p₂) =
      (8 : MvPolynomial (Fin 2) ℚ) • ((X 0 : MvPolynomial (Fin 2) ℚ) • q₂ -
        (X 1 : MvPolynomial (Fin 2) ℚ) • q₁) := by
    simp only [integerCoefficientMap, map_X] at h₁ h₂
    simp only [integerPolynomialMap, Polynomial.map_sub, Polynomial.map_smul,
      integerCoefficientMap, map_X]
    change (X 1 : MvPolynomial (Fin 2) ℚ) • integerPolynomialMap (b4Operator (X 0) p₁) -
      (X 0 : MvPolynomial (Fin 2) ℚ) • integerPolynomialMap (b4Operator (X 1) p₂) = _
    simp only [Polynomial.smul_eq_C_mul, map_ofNat] at h₁ h₂ hz ⊢
    linear_combination 4*hz - Polynomial.C (X (1 : Fin 2))*h₁ +
      Polynomial.C (X (0 : Fin 2))*h₂
  have hd := eight_dvd_polynomial_of_remainder _ _
    (coeffTwoIntegral_sub (coeffTwoIntegral_X_smul 0 hq₂)
      (coeffTwoIntegral_X_smul 1 hq₁)) he
  obtain ⟨r, hr⟩ := hd
  refine ⟨(finSuccEquiv ℤ 2).symm r, ?_⟩
  change (finSuccEquiv ℤ 2).symm _ = _
  rw [hr, map_mul, map_ofNat]

end TernaryPoly.IntegerToddNumerator
