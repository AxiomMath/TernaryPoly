module

public import TernaryPeriodPolynomials.Polynomial.NormKernel.QuotientBasis

@[expose] public section


/-!
# Appendix D: the printed Gröbner basis of `I = (d₄, d₆, d₇)`

The fourteen printed monic polynomials lie in `I` (explicit certificates
`groebnerBasis_eq_*`), generate `I`, and form a Gröbner basis of `I` for the lexicographic order
`a > b > c`: every nonzero element of `I` has leading monomial divisible by the leading monomial of
one of them (`groebnerBasis_isGroebner`). The standard monomials, those not divisible by any of the
fourteen leading monomials, are exactly the 28 printed ones (`standard_iff`).

Written by Claude Opus 5.5.
-/


noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixD

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial dicksonIdeal)

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n


/-- The printed monic Gröbner basis of `I = (d₄, d₆, d₇)` for lex `a > b > c`. -/
def groebnerBasis : Fin 14 → Poly :=
  ![a ^ 4 + a * c + b ^ 2,
    a ^ 3 * b ^ 2 + a * c ^ 2 + b ^ 2 * c,
    a ^ 3 * c + a ^ 2 * b ^ 2 + a * b * c + c ^ 2,
    a ^ 2 * b ^ 3 + a * b ^ 2 * c + b ^ 4 + b * c ^ 2,
    a ^ 2 * b * c + a * c ^ 2,
    a ^ 2 * c ^ 2 + b ^ 4,
    a * b ^ 4 + c ^ 3,
    a * b ^ 3 * c,
    a * b * c ^ 2 + b ^ 3 * c + c ^ 3,
    a * c ^ 3 + b ^ 5,
    b ^ 6,
    b ^ 4 * c + b * c ^ 3,
    b ^ 2 * c ^ 2,
    c ^ 4]

theorem groebnerBasis_cert_0 : (a ^ 4 + a * c + b ^ 2 : Poly) =
    (1) * d4 + (0) * d6 + (0) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf

theorem groebnerBasis_cert_1 : (a ^ 3 * b ^ 2 + a * c ^ 2 + b ^ 2 * c : Poly) =
    (c) * d4 + (a) * d6 + (1) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_2 : (a ^ 3 * c + a ^ 2 * b ^ 2 + a * b * c + c ^ 2 : Poly) =
    (0) * d4 + (1) * d6 + (0) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf

theorem groebnerBasis_cert_3 : (a ^ 2 * b ^ 3 + a * b ^ 2 * c + b ^ 4 + b * c ^ 2 : Poly) =
    (a * c + b ^ 2) * d4 + (a ^ 2 + b) * d6 + (0) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_4 : (a ^ 2 * b * c + a * c ^ 2 : Poly) =
    (0) * d4 + (0) * d6 + (1) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf

theorem groebnerBasis_cert_5 : (a ^ 2 * c ^ 2 + b ^ 4 : Poly) =
    (a * c + b ^ 2) * d4 + (a ^ 2) * d6 + (a) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_6 : (a * b ^ 4 + c ^ 3 : Poly) =
    (a ^ 2 * c + a * b ^ 2) * d4 + (a ^ 3 + c) * d6 + (a ^ 2 + b) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_7 : (a * b ^ 3 * c : Poly) =
    (a * b * c) * d4 + (a * c) * d6 + (a ^ 3 + a * b + c) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_8 : (a * b * c ^ 2 + b ^ 3 * c + c ^ 3 : Poly) =
    (b * c) * d4 + (c) * d6 + (a ^ 2 + b) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_9 : (a * c ^ 3 + b ^ 5 : Poly) =
    (a * b * c + b ^ 3) * d4 + (a ^ 2 * b) * d6 + (a * b + c) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_10 : (b ^ 6 : Poly) =
    (a ^ 2 * c ^ 2 + a * b ^ 2 * c + b ^ 4) * d4 + (a ^ 3 * c + a ^ 2 * b ^ 2) * d6 + (a ^ 3 * b + a * b ^ 2) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_11 : (b ^ 4 * c + b * c ^ 3 : Poly) =
    (a * c ^ 2 + b ^ 2 * c) * d4 + (a ^ 2 * c + b * c) * d6 + (b ^ 2) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_12 : (b ^ 2 * c ^ 2 : Poly) =
    (c ^ 2) * d4 + (a * c) * d6 + (a * b) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem groebnerBasis_cert_13 : (c ^ 4 : Poly) =
    (a ^ 2 * c ^ 2) * d4 + (a ^ 3 * c + a * b * c + c ^ 2) * d6 + (a ^ 3 * b + a ^ 2 * c + a * b ^ 2) * d7 := by
  rw [← sub_eq_zero]
  simp only [d4, d6, d7, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem mem_of_cert {x p q r : Poly} (h : x = p * d4 + q * d6 + r * d7) :
    x ∈ dicksonIdeal :=
  (mem_dicksonIdeal_iff x).mpr ⟨p, q, r, h⟩

/-- The fourteen polynomials lie in `I`. -/
theorem groebnerBasis_mem (i : Fin 14) : groebnerBasis i ∈ dicksonIdeal := by
  fin_cases i
  · exact mem_of_cert groebnerBasis_cert_0
  · exact mem_of_cert groebnerBasis_cert_1
  · exact mem_of_cert groebnerBasis_cert_2
  · exact mem_of_cert groebnerBasis_cert_3
  · exact mem_of_cert groebnerBasis_cert_4
  · exact mem_of_cert groebnerBasis_cert_5
  · exact mem_of_cert groebnerBasis_cert_6
  · exact mem_of_cert groebnerBasis_cert_7
  · exact mem_of_cert groebnerBasis_cert_8
  · exact mem_of_cert groebnerBasis_cert_9
  · exact mem_of_cert groebnerBasis_cert_10
  · exact mem_of_cert groebnerBasis_cert_11
  · exact mem_of_cert groebnerBasis_cert_12
  · exact mem_of_cert groebnerBasis_cert_13

end TernaryPeriodPolynomials.Argument.AppendixD
