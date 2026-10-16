module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.SymEvenNorm
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.SymIsSymmetric
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SymmetricAlternatingBasics

@[expose] public section



/-!
Alternating mirror of the base witnesses, toward `modFour_beta_triangular`'s alternating conjunct.
Mirrors `BaseCases.lean` / `BaseSymEvenNorm.lean` / `BaseSymIsSymmetric.lean` for the
alternating lift `oddGenLiftAlt` in place of the symmetric `oddGenLiftSym`.

Key shortcut: `liftDelta = liftCplus + 2 * altDelta` (pure algebra from the `liftA`,
`liftB`, `liftC` definitions, the same identity underlying `Basics.lean`'s
`reduceTwo_liftDelta`). Hence every alternating lift is the symmetric lift plus twice a
correction: `oddGenLiftAlt j = oddGenLiftSym j + 2 * WD j`, so
`baseAlt j 0 = baseSym j 0 + 2 * WD j`. Combined with `threeTermNorm`'s `ℤ`-linearity,
this gives the alternating half-witness directly from the already-known symmetric one
(`g0_sym`, i.e. `half_j_0`) plus the *raw* `threeTermNorm (WD j)` — no extra evenness
argument is needed for `WD j` itself; only its literal value (computed per `j` later) is.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- The correction term in `liftDelta = liftCplus + 2 * altDelta`. -/
noncomputable def altDelta : MvPolynomial (Fin 3) ℤ :=
  -(liftC + (X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 0 * X 1 * X 2))

theorem liftDelta_eq : liftDelta = liftCplus + 2 * altDelta := by
  simp only [liftDelta, liftCplus, altDelta, liftA, liftB, liftC]
  ring

/-- The alternating-minus-symmetric correction at the `genLift` level. -/
noncomputable def W (j : Fin 8) : MvPolynomial (Fin 3) ℤ := liftA * altDelta * basisLift j

/-- The alternating-minus-symmetric correction at the `oddGenLift` level. -/
noncomputable def WD (j : Fin 8) : MvPolynomial (Fin 3) ℤ := W j * liftD7 ^ kappa j

theorem genLiftAlt_eq_add (j : Fin 8) : genLiftAlt j = genLiftSym j + 2 * W j := by
  simp only [genLiftAlt, genLiftSym, W, liftDelta_eq]
  ring

theorem oddGenLiftAlt_eq_add (j : Fin 8) : oddGenLiftAlt j = oddGenLiftSym j + 2 * WD j := by
  simp only [oddGenLiftAlt, oddGenLiftSym, WD, genLiftAlt_eq_add]
  ring

/-- The 32 "pure quadrant" alternating base witnesses, mirroring `baseSym`. -/
noncomputable def baseAlt (j : Fin 8) (m : Fin 4) : MvPolynomial (Fin 3) ℤ :=
  mult m * oddGenLiftAlt j

theorem baseAlt_zero_eq (j : Fin 8) : baseAlt j 0 = baseSym j 0 + 2 * WD j := by
  simp only [baseAlt, baseSym, mult, Matrix.cons_val_zero, oddGenLiftAlt_eq_add]
  ring

/-- `threeTermNorm` is `ℤ`-linear: it commutes with `x ↦ x + 2 * y`. -/
theorem threeTermNorm_add_two_mul (x y : MvPolynomial (Fin 3) ℤ) :
    threeTermNorm (x + 2 * y) = threeTermNorm x + C 2 * threeTermNorm y := by
  have hc2 : (C 2 : MvPolynomial (Fin 3) ℤ) = 2 := map_ofNat C 2
  rw [hc2]
  simp only [threeTermNorm, map_add, map_mul, map_ofNat]
  ring

private theorem reduceTwo_evalSquaredLift_eq' (P : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (evalSquaredLift P) = evalR2 (reduceTwo P) :=
  reduceTwo_evalSquaredLift P

theorem reduceTwo_baseAlt (j : Fin 8) (m : Fin 4) :
    reduceTwo (baseAlt j m) = reduceTwo (mult m) * oddGenerator j := by
  simp [baseAlt, reduceTwo_oddGenLiftAlt]

theorem baseAlt_term_half (P : MvPolynomial (Fin 3) ℤ) (j : Fin 8) (m : Fin 4) :
    ∃ g : MvPolynomial (Fin 3) ℤ,
      threeTermNorm (evalSquaredLift P * baseAlt j m) = C 2 * g := by
  apply exists_half
  rw [reduceTwo_threeTermNorm, map_mul, reduceTwo_evalSquaredLift_eq', reduceTwo_baseAlt,
    show evalR2 (reduceTwo P) * (reduceTwo (mult m) * oddGenerator j)
        = (evalR2 (reduceTwo P) * reduceTwo (mult m)) * oddGenerator j by ring,
    norm_mul_invariant (by rw [map_mul, evalR2_sub1_fixed, mult_sub1_fixed])
      (by rw [map_mul, evalR2_sub2_fixed, mult_sub2_fixed]),
    oddGenerator_norm_zero, mul_zero]

theorem baseAlt_isAlternating (j : Fin 8) (m : Fin 4) :
    IsAlternating (baseAlt j m : MvPolynomial (Fin 3) ℤ) :=
  symmetric_mul_alternating (mult_isSymmetric m) (oddGenLiftAlt_isAlternating j)

/-- Alternating polynomials are closed under addition (mirrors the `private`
`isAlternating_sub` in `LiftIndependence.lean`, not reusable from here). -/
theorem isAlternating_add {s t : MvPolynomial (Fin 3) ℤ} (hs : IsAlternating s)
    (ht : IsAlternating t) : IsAlternating (s + t) := by
  intro σ
  rw [map_add, hs σ, ht σ, smul_add]

/-- The key combining lemma: the alternating base witness's half-norm is the symmetric
one's half-norm plus the raw `threeTermNorm (WD j)`. -/
theorem baseAlt_zero_half_pi (j : Fin 8) {g0_sym : MvPolynomial (Fin 3) ℤ}
    (h0_sym : threeTermNorm (baseSym j 0) = C 2 * g0_sym) :
    threeTermNorm (baseAlt j 0) = C 2 * (g0_sym + threeTermNorm (WD j)) := by
  rw [baseAlt_zero_eq, threeTermNorm_add_two_mul, h0_sym]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
