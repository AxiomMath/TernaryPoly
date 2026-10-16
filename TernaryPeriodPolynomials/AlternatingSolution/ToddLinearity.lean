module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

/-- Substitution turns a power of the coordinate sum into a power of the frame sum. -/
theorem substitute3_W_pow_mul (r : ℕ) (f a b c : TernaryPolynomial) :
    substitute3 ((X 0+X 1+X 2)^r * f) a b c =
      (a+b+c)^r * substitute3 f a b c := by
  simp [substitute3]

/-- The first alternating frame sends `W` to `Z-3Y`. -/
theorem alternatingFrame1_W_pow_mul (r : ℕ) (f : TernaryPolynomial) :
    alternatingFrame1 ((X 0+X 1+X 2)^r * f) =
      (X 2-3*X 1)^r * alternatingFrame1 f := by
  have hsum : (X 2-2*X 1)+(-X 0)+(X 0-X 1) =
      (X 2-3*X 1 : TernaryPolynomial) := by ring
  simp only [alternatingFrame1, substitute3_W_pow_mul, hsum]

/-- All three summands in the second alternating frame have the same coordinate sum. -/
theorem alternatingFrame2_W_pow_mul (r : ℕ) (f : TernaryPolynomial) :
    alternatingFrame2 ((X 0+X 1+X 2)^r * f) =
      (X 2-3*X 1)^r * alternatingFrame2 f := by
  have hsum2 : (X 2-X 0)+(X 0-2*X 1)+(-X 1) =
      (X 2-3*X 1 : TernaryPolynomial) := by ring
  have hsum3 : (X 2-2*X 1)+(X 1-X 0)+(X 0-2*X 1) =
      (X 2-3*X 1 : TernaryPolynomial) := by ring
  simp only [alternatingFrame2, alternatingFrame1_W_pow_mul,
    substitute3_W_pow_mul, hsum2, hsum3]
  ring

/-- Ternary Todd is linear over polynomials independent of the first coordinate. -/
theorem ternaryTodd_mul_of_coefficient (u q : MvPolynomial (Fin 2) ℚ)
    (c f : TernaryPolynomial) (hc : finSuccEquiv ℚ 2 c = Polynomial.C q) :
    ternaryTodd u (c*f) = c * ternaryTodd u f := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd, AlgEquiv.apply_symm_apply, map_mul, hc]
  simp only [← Polynomial.smul_eq_C_mul, map_smul]

/-- Powers of `Z-3Y` are coefficient scalars for every ternary Todd parameter. -/
theorem ternaryTodd_Z_sub_three_Y_pow_mul (u : MvPolynomial (Fin 2) ℚ)
    (r : ℕ) (f : TernaryPolynomial) :
    ternaryTodd u ((X 2-3*X 1)^r * f) =
      (X 2-3*X 1)^r * ternaryTodd u f := by
  apply ternaryTodd_mul_of_coefficient u ((X 1-3*X 0)^r)
  simp only [map_pow, map_sub, map_mul, map_ofNat,
    finSuccEquiv_ternary_X_one, finSuccEquiv_ternary_X_two]

/-- Multiplying by a power of `W` scales the actual alternating Todd expression by `(Z-3Y)^r`. -/
theorem alternatingTodd_W_pow_mul (r : ℕ) (f : TernaryPolynomial) :
    alternatingTodd ((X 0+X 1+X 2)^r * f) =
      (X 2-3*X 1)^r * alternatingTodd f := by
  simp only [alternatingTodd, alternatingFrame1_W_pow_mul,
    alternatingFrame2_W_pow_mul, ternaryTodd_Z_sub_three_Y_pow_mul]
  ring

end TernaryPoly
