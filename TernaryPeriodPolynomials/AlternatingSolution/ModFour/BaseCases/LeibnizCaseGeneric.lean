module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.LeibnizAssembly
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases

@[expose] public section



/-!
# Generic Leibniz shortcut for quadrants `m = 1, 2, 3` of the `W(j,m)` table

`baseSym j 1 = liftD6 * baseSym j 0`, `baseSym j 2 = liftD4 * baseSym j 0`, and
`baseSym j 3 = liftD4 * liftD6 * baseSym j 0` (immediate from `mult`'s definition), and
`reduceTwo (baseSym j 0) = oddGenerator j` (from `reduceTwo_oddGenLiftSym`, since
`mult 0 = 1`). So the already-proven generic Leibniz-defect lemmas `beta_mul_D4`,
`beta_mul_D6`, `beta_mul_D4D6` (`LeibnizAssembly.lean`) turn any already-established
`half_j_0`-shaped fact directly into the `m = 1, 2, 3` cases for that same `j`, at the cost
of only the two mod-two defect values `delta_p (oddGenerator j)`, `delta_q (oddGenerator j)` —
no further `exists_half`/large-`ring` derivation is needed for `m = 1, 2, 3`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem baseSym_one_eq (j : Fin 8) : liftD6 * baseSym j 0 = baseSym j 1 := by
  simp [baseSym, mult]

theorem baseSym_two_eq (j : Fin 8) : liftD4 * baseSym j 0 = baseSym j 2 := by
  simp [baseSym, mult]

theorem baseSym_three_eq (j : Fin 8) : liftD4 * liftD6 * baseSym j 0 = baseSym j 3 := by
  simp [baseSym, mult]

theorem reduceTwo_baseSym_zero (j : Fin 8) : reduceTwo (baseSym j 0) = oddGenerator j := by
  simp [baseSym, mult, reduceTwo_oddGenLiftSym]

/-- Generic shortcut for quadrant `m = 1`: from a `half_j_0`-shaped fact, derive the `(j,1)`
case directly via `beta_mul_D6`, with the Leibniz defect isolated as `delta_q (oddGenerator j)`. -/
theorem case_j1_generic {j : Fin 8} {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseSym j 0) = C 2 * g0) :
    threeTermNorm (baseSym j 1)
      = C 2 * (liftD6 * g0 + E1_D6 * bind₁ A1vec (baseSym j 0)
          + E2_D6 * bind₁ A2vec (baseSym j 0)) ∧
    piOperator (reduceTwo (liftD6 * g0 + E1_D6 * bind₁ A1vec (baseSym j 0)
          + E2_D6 * bind₁ A2vec (baseSym j 0)))
      = d6 * piOperator (reduceTwo g0) + delta_q (oddGenerator j) := by
  obtain ⟨hnorm, hpi⟩ := beta_mul_D6 h0
  rw [baseSym_one_eq j] at hnorm
  rw [reduceTwo_baseSym_zero j] at hpi
  exact ⟨hnorm, hpi⟩

/-- Generic shortcut for quadrant `m = 2`, via `beta_mul_D4`. -/
theorem case_j2_generic {j : Fin 8} {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseSym j 0) = C 2 * g0) :
    threeTermNorm (baseSym j 2)
      = C 2 * (liftD4 * g0 + E1_D4 * bind₁ A1vec (baseSym j 0)
          + E2_D4 * bind₁ A2vec (baseSym j 0)) ∧
    piOperator (reduceTwo (liftD4 * g0 + E1_D4 * bind₁ A1vec (baseSym j 0)
          + E2_D4 * bind₁ A2vec (baseSym j 0)))
      = d4 * piOperator (reduceTwo g0) + delta_p (oddGenerator j) := by
  obtain ⟨hnorm, hpi⟩ := beta_mul_D4 h0
  rw [baseSym_two_eq j] at hnorm
  rw [reduceTwo_baseSym_zero j] at hpi
  exact ⟨hnorm, hpi⟩

/-- Generic shortcut for quadrant `m = 3`, via `beta_mul_D4D6`. -/
theorem case_j3_generic {j : Fin 8} {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseSym j 0) = C 2 * g0) :
    threeTermNorm (baseSym j 3)
      = C 2 * (liftD4 * liftD6 * g0 + E1_D4D6 * bind₁ A1vec (baseSym j 0)
          + E2_D4D6 * bind₁ A2vec (baseSym j 0)) ∧
    piOperator (reduceTwo (liftD4 * liftD6 * g0 + E1_D4D6 * bind₁ A1vec (baseSym j 0)
          + E2_D4D6 * bind₁ A2vec (baseSym j 0)))
      = d4 * d6 * piOperator (reduceTwo g0)
          + d4 * delta_q (oddGenerator j) + d6 * delta_p (oddGenerator j) := by
  obtain ⟨hnorm, hpi⟩ := beta_mul_D4D6 h0
  rw [baseSym_three_eq j] at hnorm
  rw [reduceTwo_baseSym_zero j] at hpi
  exact ⟨hnorm, hpi⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
