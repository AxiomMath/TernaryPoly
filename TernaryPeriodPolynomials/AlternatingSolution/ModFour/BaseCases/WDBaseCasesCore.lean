module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.AltBasics
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.ThreeTermNormReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SquaredLiftInvariance
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section



/-! Shared infrastructure for `WDBaseCases0.lean` .. `WDBaseCases7.lean`
(`BaseAltBasics.lean`'s `WD j = W j * liftD7 ^ kappa j`, the raw quantity whose
`threeTermNorm` enters `baseAlt_zero_half_pi`'s half-witness with no extra evenness
argument needed).

Rather than forming `threeTermNorm (WD j)` as a huge-coefficient integer literal, this pushes `reduceTwo` through the algebra *first*, landing in a degree-≤9
characteristic-two computation:

  piOperator (reduceTwo (threeTermNorm (WD j)))
    = piOperator (norm (reduceTwo (WD j)))                      [`reduceTwo_threeTermNorm`]
    = piOperator (norm (d7 ^ kappa j * reduceTwo (W j)))         [`reduceTwo_WD`]
    = piOperator (d7 ^ kappa j * norm (reduceTwo (W j)))         [`d7` fixed by `sub₁`, `sub₂`]
    = d7 ^ kappa j * piOperator (norm (reduceTwo (W j)))         [`d7` fixed by `piSubstitutions`]
    = d7 ^ kappa j * generator j                                 [core per-`j` identity]
    = oddGenerator j                                             [definitional]

`pi_reduceTwo_threeTermNorm_WD_of_core` assembles this chain; each `WDBaseCasesJ.lean`
file supplies only the core identity `piOperator (norm (reduceTwo (W j))) = generator j`
(with `reduceTwo (W j) = a * δ̄ * basis j`, `δ̄ := reduceTwo altDelta` an explicit degree-2
polynomial), at the same order of magnitude as the already-closed `pi_4_2`
(`BaseCases9.lean`). -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! ### Infrastructure: `d7` (hence `d7 ^ k`) is fixed by `sub₁`, `sub₂`, and every
`piSubstitutions` element, re-derived here since the `SquaredLiftInvariance.lean` copies
are file-`private`. -/

private theorem sub1_fixes_d7 : TernaryPoly.CharTwoNorm.sub₁ d7 = d7 := by
  simpa [TernaryPoly.CharTwoNorm.invariant] using TernaryPoly.CharTwoNorm.sub₁_invariant 2

private theorem sub2_fixes_d7 : TernaryPoly.CharTwoNorm.sub₂ d7 = d7 := by
  simpa [TernaryPoly.CharTwoNorm.invariant] using TernaryPoly.CharTwoNorm.sub₂_invariant 2

theorem sub1_fixes_d7_pow (k : ℕ) : TernaryPoly.CharTwoNorm.sub₁ (d7 ^ k) = d7 ^ k := by
  rw [map_pow, sub1_fixes_d7]

theorem sub2_fixes_d7_pow (k : ℕ) : TernaryPoly.CharTwoNorm.sub₂ (d7 ^ k) = d7 ^ k := by
  rw [map_pow, sub2_fixes_d7]

private theorem pi_fixes_d7 {t : Fin 3 → Poly2} (ht : t ∈ piSubstitutions) :
    bind₁ t d7 = d7 := by
  simpa [TernaryPoly.CharTwoNorm.invariant] using piSubstitutions_invariant t ht 2

theorem pi_fixes_d7_pow {t : Fin 3 → Poly2} (ht : t ∈ piSubstitutions) (k : ℕ) :
    bind₁ t (d7 ^ k) = d7 ^ k := by
  rw [map_pow, pi_fixes_d7 ht]

/-- `reduceTwo (WD j)`, factoring out `d7 ^ kappa j` on the left (matching
`norm_mul_of_fixed`/`piOperator_mul_of_fixed`'s expected `Q * h` shape). -/
theorem reduceTwo_WD (j : Fin 8) :
    reduceTwo (WD j) = d7 ^ kappa j * reduceTwo (W j) := by
  show reduceTwo (W j * liftD7 ^ kappa j) = d7 ^ kappa j * reduceTwo (W j)
  rw [map_mul, map_pow, reduceTwo_liftD7]
  ring

/-- `altDelta` reduced mod two: the explicit degree-2 correction polynomial `δ̄`. -/
theorem reduceTwo_altDelta :
    reduceTwo altDelta =
      c + (X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 0 * X 1 * X 2) := by
  simp [altDelta, reduceTwo_liftC, CharTwo.neg_eq]
  ring

/-- `W j` reduced mod two: `a * δ̄ * basis j`. -/
theorem reduceTwo_W (j : Fin 8) :
    reduceTwo (W j) =
      a * (c + (X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 0 * X 1 * X 2)) * basis j := by
  show reduceTwo (liftA * altDelta * basisLift j) = _
  rw [map_mul, map_mul, reduceTwo_liftA, reduceTwo_altDelta, reduceTwo_basisLift]

/-- Assembles the five-step chain in the header comment from the core per-`j` identity. -/
theorem pi_reduceTwo_threeTermNorm_WD_of_core {j : Fin 8}
    (hcore : piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W j))) = generator j) :
    piOperator (reduceTwo (threeTermNorm (WD j))) = oddGenerator j := by
  rw [reduceTwo_threeTermNorm, reduceTwo_WD,
    TernaryPoly.CharTwoNorm.norm_mul_of_fixed _ _ (sub1_fixes_d7_pow (kappa j))
      (sub2_fixes_d7_pow (kappa j)),
    piOperator_mul_of_fixed (fun t ht => pi_fixes_d7_pow ht (kappa j)), hcore]
  simp only [oddGenerator]
  ring

section Reflection

open PolynomialReflection

/-- `δ̄ = c + (x²z + xy² + yz² + xyz)` as an exponent list. -/
def deltaBarL : List Mon := addL cL [(0, 1, 2), (1, 1, 1), (1, 2, 0), (2, 0, 1)]

theorem ev_deltaBar :
    ev deltaBarL = c + (X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 0 * X 1 * X 2) := by
  rw [deltaBarL, ev_addL, ev_c]
  simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- The core identity of the case `j`, checked on exponent lists. -/
theorem core_of_reflect (j : Fin 8)
    (h : piL (normL (mulL (mulL aL deltaBarL) (basisL j))) = generatorL j) :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W j))) = generator j := by
  rw [reduceTwo_W, ← ev_a, ← ev_deltaBar, ← ev_basis, ← ev_mulL, ← ev_mulL, ev_norm,
    piOperator_ev, h, ev_generator]

end Reflection

end TernaryPeriodPolynomials.Argument.ModFourBeta
