module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GeneratorAbstract

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open TernaryPoly.DicksonQuotient (a b c d4 d6 d7 standardMonomial Poly)

-- Hand-derived candidate decompositions of each `genAbs i` into
-- `invariant-level-factor * standardMonomial j` terms, to be checked by `ring`.
-- Pivot indices: 9,13,16,18,20,23,24,26 for i=0..7 respectively.

-- `ring` normalizes but does not fold numeral coefficients modulo the ambient ring's
-- characteristic (it has no reason to, since that is *not* a generic `CommRing` fact).
-- These four facts close exactly that gap for `Poly = MvPolynomial (Fin 3) (ZMod 2)`.
private theorem two_eq_zero : (2 : Poly) = 0 := by
  have h : ((2 : ℕ) : Poly) = 0 := (CharP.cast_eq_zero_iff Poly 2 2).mpr (by norm_num)
  simpa using h

private theorem four_eq_zero : (4 : Poly) = 0 := by
  have h : ((4 : ℕ) : Poly) = 0 := (CharP.cast_eq_zero_iff Poly 2 4).mpr (by norm_num)
  simpa using h

private theorem three_eq_one : (3 : Poly) = 1 := by
  have h : (3 : Poly) = 2 + 1 := by norm_num
  rw [h, two_eq_zero, zero_add]

private theorem five_eq_one : (5 : Poly) = 1 := by
  have h : (5 : Poly) = 4 + 1 := by norm_num
  rw [h, four_eq_zero, zero_add]

theorem genAbs0_decomp : genAbs 0 = standardMonomial 8 + standardMonomial 9 := by
  simp [genAbs, cplusAbs, basisAbs, standardMonomial, a, b, c]
  ring

theorem genAbs1_decomp : genAbs 1 = standardMonomial 12 + standardMonomial 13 := by
  simp [genAbs, cplusAbs, basisAbs, standardMonomial, a, b, c]
  ring

theorem genAbs2_decomp :
    genAbs 2 = d6 * standardMonomial 0 + d4 * standardMonomial 2 +
      standardMonomial 14 + standardMonomial 15 + standardMonomial 16 := by
  simp [genAbs, cplusAbs, basisAbs, d4, d6, standardMonomial, a, b, c]
  ring_nf
  simp [two_eq_zero, three_eq_one]

theorem genAbs3_decomp :
    genAbs 3 = d6 * standardMonomial 1 + d4 * standardMonomial 4 + standardMonomial 18 := by
  simp [genAbs, cplusAbs, basisAbs, d4, d6, standardMonomial, a, b, c]
  ring_nf
  simp [two_eq_zero]

theorem genAbs4_decomp :
    genAbs 4 = d4 * standardMonomial 4 + d4 * standardMonomial 5 +
      standardMonomial 18 + standardMonomial 20 := by
  simp [genAbs, cplusAbs, basisAbs, d4, standardMonomial, a, b, c]
  ring_nf
  simp [two_eq_zero]

theorem genAbs5_decomp :
    genAbs 5 = d7 * standardMonomial 1 + d6 * standardMonomial 3 +
      d4 * standardMonomial 8 + standardMonomial 23 := by
  simp [genAbs, cplusAbs, basisAbs, d4, d6, d7, standardMonomial, a, b, c]
  ring_nf
  simp [two_eq_zero, three_eq_one]

theorem genAbs6_decomp :
    genAbs 6 = d6 * standardMonomial 4 + d6 * standardMonomial 5 + d6 * standardMonomial 6 +
      d4 * standardMonomial 13 + standardMonomial 24 := by
  simp [genAbs, cplusAbs, basisAbs, d4, d6, standardMonomial, a, b, c]
  ring_nf
  simp [two_eq_zero, three_eq_one]

theorem genAbs7_decomp :
    genAbs 7 = d4 * d6 * standardMonomial 0 + d4 * d4 * standardMonomial 2 +
      d7 * standardMonomial 6 + d6 * standardMonomial 7 +
      d4 * standardMonomial 16 + d4 * standardMonomial 17 + standardMonomial 26 := by
  simp [genAbs, cplusAbs, basisAbs, d4, d6, d7, standardMonomial, a, b, c]
  ring_nf
  simp [two_eq_zero, three_eq_one, four_eq_zero, five_eq_one]

end TernaryPeriodPolynomials.Argument.CharTwoKernel
