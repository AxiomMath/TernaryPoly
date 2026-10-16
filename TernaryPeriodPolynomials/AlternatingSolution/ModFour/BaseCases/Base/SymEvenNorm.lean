module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EvalR2Fixed
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.ThreeTermNormReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SquaredLiftInvariance

@[expose] public section



/-!
`evalSquaredLift P * baseSym j m` always has even `threeTermNorm`, for any integral `P`,
`j : Fin 8`, `m : Fin 4`. This is the norm-evenness fact needed to apply
`lemma_5_5_clause4` to each quadrant piece of the `vpiece j` construction for `modFour_beta_triangular`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem reduceTwo_evalSquaredLift_eq (P : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (evalSquaredLift P) = evalR2 (reduceTwo P) :=
  reduceTwo_evalSquaredLift P

/-- `reduceTwo (mult m)` is fixed by `sub₁`. -/
theorem mult_sub1_fixed (m : Fin 4) : sub₁ (reduceTwo (mult m)) = reduceTwo (mult m) := by
  fin_cases m <;> simp [mult, reduceTwo_liftD4, reduceTwo_liftD6, sub1_d4', sub1_d6']

/-- `reduceTwo (mult m)` is fixed by `sub₂`. -/
theorem mult_sub2_fixed (m : Fin 4) : sub₂ (reduceTwo (mult m)) = reduceTwo (mult m) := by
  fin_cases m <;> simp [mult, reduceTwo_liftD4, reduceTwo_liftD6, sub2_d4', sub2_d6']

/-- `reduceTwo (baseSym j m) = reduceTwo (mult m) * oddGenerator j`. -/
theorem reduceTwo_baseSym (j : Fin 8) (m : Fin 4) :
    reduceTwo (baseSym j m) = reduceTwo (mult m) * oddGenerator j := by
  simp [baseSym, reduceTwo_oddGenLiftSym]

/-- `evalSquaredLift P * baseSym j m` always has even `threeTermNorm`. -/
theorem baseSym_term_half (P : MvPolynomial (Fin 3) ℤ) (j : Fin 8) (m : Fin 4) :
    ∃ g : MvPolynomial (Fin 3) ℤ,
      threeTermNorm (evalSquaredLift P * baseSym j m) = C 2 * g := by
  apply exists_half
  rw [reduceTwo_threeTermNorm, map_mul, reduceTwo_evalSquaredLift_eq, reduceTwo_baseSym,
    show evalR2 (reduceTwo P) * (reduceTwo (mult m) * oddGenerator j)
        = (evalR2 (reduceTwo P) * reduceTwo (mult m)) * oddGenerator j by ring,
    norm_mul_invariant (by rw [map_mul, evalR2_sub1_fixed, mult_sub1_fixed])
      (by rw [map_mul, evalR2_sub2_fixed, mult_sub2_fixed]),
    oddGenerator_norm_zero, mul_zero]

end TernaryPeriodPolynomials.Argument.ModFourBeta
