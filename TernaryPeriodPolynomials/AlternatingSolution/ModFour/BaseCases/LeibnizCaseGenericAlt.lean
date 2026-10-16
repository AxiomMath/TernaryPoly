module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.LeibnizAssembly
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.AltBasics

@[expose] public section



/-!
Alternating mirror of `LeibnizCaseGeneric.lean`: the three "one Leibniz-multiplier"
cases (`D₆`, `D₄`, `D₄D₆`) for the alternating base witness `baseAlt`, reusing
`beta_mul_D4`/`beta_mul_D6`/`beta_mul_D4D6` from `LeibnizAssembly.lean` unchanged (those
are generic over any `v`/`g` pair with `threeTermNorm v = C 2 * g`).
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem baseAlt_one_eq (j : Fin 8) : liftD6 * baseAlt j 0 = baseAlt j 1 := by
  simp [baseAlt, mult]

theorem baseAlt_two_eq (j : Fin 8) : liftD4 * baseAlt j 0 = baseAlt j 2 := by
  simp [baseAlt, mult]

theorem baseAlt_three_eq (j : Fin 8) : liftD4 * liftD6 * baseAlt j 0 = baseAlt j 3 := by
  simp [baseAlt, mult]

theorem reduceTwo_baseAlt_zero (j : Fin 8) : reduceTwo (baseAlt j 0) = oddGenerator j := by
  simp [baseAlt, mult, reduceTwo_oddGenLiftAlt]

theorem case_j1_generic_alt {j : Fin 8} {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseAlt j 0) = C 2 * g0) :
    threeTermNorm (baseAlt j 1)
      = C 2 * (liftD6 * g0 + E1_D6 * bind₁ A1vec (baseAlt j 0)
          + E2_D6 * bind₁ A2vec (baseAlt j 0)) ∧
    piOperator (reduceTwo (liftD6 * g0 + E1_D6 * bind₁ A1vec (baseAlt j 0)
          + E2_D6 * bind₁ A2vec (baseAlt j 0)))
      = d6 * piOperator (reduceTwo g0) + delta_q (oddGenerator j) := by
  obtain ⟨hnorm, hpi⟩ := beta_mul_D6 h0
  rw [baseAlt_one_eq j] at hnorm
  rw [reduceTwo_baseAlt_zero j] at hpi
  exact ⟨hnorm, hpi⟩

theorem case_j2_generic_alt {j : Fin 8} {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseAlt j 0) = C 2 * g0) :
    threeTermNorm (baseAlt j 2)
      = C 2 * (liftD4 * g0 + E1_D4 * bind₁ A1vec (baseAlt j 0)
          + E2_D4 * bind₁ A2vec (baseAlt j 0)) ∧
    piOperator (reduceTwo (liftD4 * g0 + E1_D4 * bind₁ A1vec (baseAlt j 0)
          + E2_D4 * bind₁ A2vec (baseAlt j 0)))
      = d4 * piOperator (reduceTwo g0) + delta_p (oddGenerator j) := by
  obtain ⟨hnorm, hpi⟩ := beta_mul_D4 h0
  rw [baseAlt_two_eq j] at hnorm
  rw [reduceTwo_baseAlt_zero j] at hpi
  exact ⟨hnorm, hpi⟩

theorem case_j3_generic_alt {j : Fin 8} {g0 : MvPolynomial (Fin 3) ℤ}
    (h0 : threeTermNorm (baseAlt j 0) = C 2 * g0) :
    threeTermNorm (baseAlt j 3)
      = C 2 * (liftD4 * liftD6 * g0 + E1_D4D6 * bind₁ A1vec (baseAlt j 0)
          + E2_D4D6 * bind₁ A2vec (baseAlt j 0)) ∧
    piOperator (reduceTwo (liftD4 * liftD6 * g0 + E1_D4D6 * bind₁ A1vec (baseAlt j 0)
          + E2_D4D6 * bind₁ A2vec (baseAlt j 0)))
      = d4 * d6 * piOperator (reduceTwo g0)
        + d4 * delta_q (oddGenerator j) + d6 * delta_p (oddGenerator j) := by
  obtain ⟨hnorm, hpi⟩ := beta_mul_D4D6 h0
  rw [baseAlt_three_eq j] at hnorm
  rw [reduceTwo_baseAlt_zero j] at hpi
  exact ⟨hnorm, hpi⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
