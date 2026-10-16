module

public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenAlgebra
public import TernaryPeriodPolynomials.Polynomial.Restriction

@[expose] public section


/-!
# `LinearIndependent` clause of `example_degree_ten`'s first conjunct

`symmetricTenSolution F` and `alternatingTenSolution F` are linearly independent over any
characteristic-zero field `F`. The route is `restriction : Ternary R → Binary R`
(`TernaryPoly.Paper.Restriction`), a linear map with `restriction ∘ cyclicLift = id` on inputs
satisfying `PeriodRelations`. Applying it turns a dependency in the ternary solution space into
one between `symmetricTenPeriod F` and `alternatingTenPeriod F`; applying the sign-flip
substitution `X 0 ↦ -X 0` a second time separates the odd and even parts, and both periods are
nonzero (checked directly by evaluating at `(3, 1)`).

This closes the `LinearIndependent` clause of `example_degree_ten`'s first conjunct, for every
`CharZero` field, independently of any cusp-form machinery. It does **not** close the remaining
`Submodule.span F {symmetricTenSolution F, alternatingTenSolution F} = solutionSpace F 10` clause
of that same conjunct: that needs an upper bound (ideally an exact value of 2) on
`Module.finrank F (solutionSpace F 10)`, and no numeric dimension fact for `solutionSpace` exists
anywhere in the repository (only the base-change invariance in
`TernaryPoly.Paper.CoefficientBaseChange`).
-/


open MvPolynomial TernaryPoly.Paper TernaryPeriodPolynomials.Argument

noncomputable section

variable (F : Type*) [Field F] [CharZero F]

theorem symmetricTenPeriod_ne_zero' : symmetricTenPeriod F ≠ 0 := by
  intro h
  have heval : MvPolynomial.eval (![3, 1] : Fin 2 → F) (symmetricTenPeriod F) = 0 := by
    rw [h, map_zero]
  simp only [symmetricTenPeriod, map_mul, map_sub, map_pow, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  norm_num at heval

theorem alternatingTenPeriod_ne_zero' : alternatingTenPeriod F ≠ 0 := by
  intro h
  have heval : MvPolynomial.eval (![3, 1] : Fin 2 → F) (alternatingTenPeriod F) = 0 := by
    rw [h, map_zero]
  simp only [alternatingTenPeriod, map_mul, map_sub, map_pow, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  norm_num at heval

omit [CharZero F] in
theorem restriction_symmetricTenSolution :
    restriction (symmetricTenSolution F) = symmetricTenPeriod F := by
  rw [symmetricTenSolution, restriction_cyclicLift symmetricTenPeriod_periodRelations]

omit [CharZero F] in
theorem restriction_alternatingTenSolution :
    restriction (alternatingTenSolution F) = alternatingTenPeriod F := by
  rw [alternatingTenSolution, restriction_cyclicLift alternatingTenPeriod_periodRelations]

omit [CharZero F] in
theorem restriction_add' (f g : Ternary F) :
    restriction (f + g) = restriction f + restriction g := by
  simp only [restriction, map_add]

omit [CharZero F] in
theorem restriction_smul' (c : F) (f : Ternary F) :
    restriction (c • f) = c • restriction f := by
  simp only [restriction, map_smul]

omit [CharZero F] in
theorem restriction_zero' : restriction (0 : Ternary F) = 0 := by
  simp only [restriction, map_zero]

/-- **Conjunct 1, `LinearIndependent` clause.** `symmetricTenSolution F` and
`alternatingTenSolution F` are linearly independent over any characteristic-zero field `F`.
Applying `restriction` (a linear map with `restriction ∘ cyclicLift = id` on period-relation
inputs) turns a dependency in the ternary solution space into one between
`symmetricTenPeriod F` and `alternatingTenPeriod F`; applying the sign-flip substitution
`X 0 ↦ -X 0` a second time separates the odd and even parts, and both periods are nonzero. -/
theorem linearIndependent_tenSolution :
    LinearIndependent F ![symmetricTenSolution F, alternatingTenSolution F] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hres : restriction (s • symmetricTenSolution F + t • alternatingTenSolution F) = 0 := by
    rw [hst]; exact restriction_zero' F
  rw [restriction_add' F, restriction_smul' F, restriction_smul' F,
    restriction_symmetricTenSolution, restriction_alternatingTenSolution,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul] at hres
  have hflip : bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) F)
      (C s * symmetricTenPeriod F + C t * alternatingTenPeriod F) = 0 := by rw [hres, map_zero]
  rw [map_add, map_mul, map_mul, bind₁_C_right, bind₁_C_right, symmetricTenPeriod_oddX,
    alternatingTenPeriod_evenX] at hflip
  have halt : (2 : MvPolynomial (Fin 2) F) * (C t * alternatingTenPeriod F) = 0 := by
    linear_combination hres + hflip
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp halt with h2 | hct
    · exact absurd h2 (by norm_num)
    · rcases mul_eq_zero.mp hct with hc | ha
      · exact (MvPolynomial.C_inj F t 0).mp (hc.trans (map_zero C).symm)
      · exact absurd ha (alternatingTenPeriod_ne_zero' F)
  have hsym : C s * symmetricTenPeriod F = 0 := by
    rw [ht0, map_zero, zero_mul, add_zero] at hres; exact hres
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hsym with hc | hs
    · exact (MvPolynomial.C_inj F s 0).mp (hc.trans (map_zero C).symm)
    · exact absurd hs (symmetricTenPeriod_ne_zero' F)
  exact ⟨hs0, ht0⟩

end
