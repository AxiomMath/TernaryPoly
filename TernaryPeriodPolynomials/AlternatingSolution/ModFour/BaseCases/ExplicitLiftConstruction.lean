module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Basics
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SymmetricAlternatingBasics
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.ThreeTermNormReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ExpandOddNormZero

@[expose] public section



/-!
# Lemma 5.5, clause 1 (existence of symmetric/alternating integral lifts, even norm)

For every `r : Fin 8 → Poly2`, builds an explicit symmetric lift `liftSym r` and an explicit
alternating lift `liftAlt r` of `expandOdd r`, each with even `threeTermNorm`.

Recipe (mirrors `TernaryPoly.CharTwoNorm.basis/generator`): `basisLift j` lifts `basis j`;
`genLiftSym j = liftA * liftCplus * basisLift j` and `genLiftAlt j = liftA * liftDelta *
basisLift j` both reduce to `generator j` (since `liftCplus, liftDelta` both reduce to `cplus`)
and are respectively symmetric/alternating; `oddGenLiftSym/Alt j = genLiftSym/Alt j *
liftD7 ^ kappa j` lift `oddGenerator j`; each coefficient `r j` is lifted via
`coeffLiftOf r j = bind₁ ![liftD4, liftD6, liftD7 ^ 2] (choice of integral lift of `r j`)`,
which is automatically symmetric regardless of the chosen lift
(`bind₁_isSymmetric_of_symmetric`) and reduces to `evalR0 (r j)`; summing
`coeffLiftOf r j * oddGenLiftSym/Alt j` over `j` gives `liftSym/Alt r`, which reduces to
`expandOdd r` and is symmetric/alternating. Evenness of the norm follows from
`reduceTwo_threeTermNorm` and `expandOdd_norm_zero`.
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus basis generator d4 d6 d7)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- Integral lift of `TernaryPoly.CharTwoNorm.basis`. -/
noncomputable def basisLift : Fin 8 → MvPolynomial (Fin 3) ℤ :=
  ![1, liftA, liftA ^ 2 + liftB, liftA * liftB, liftA ^ 3 + liftC, liftA * liftCplus,
    liftA ^ 3 * (liftA ^ 2 + liftB), liftA ^ 6 + liftA ^ 3 * liftC + liftB ^ 3 + liftC ^ 2]

theorem reduceTwo_basisLift (i : Fin 8) : reduceTwo (basisLift i) = basis i := by
  fin_cases i <;>
    simp [basisLift, basis, map_add, map_mul, map_pow, reduceTwo_liftA, reduceTwo_liftB,
      reduceTwo_liftC, reduceTwo_liftCplus]

theorem basisLift_isSymmetric (i : Fin 8) :
    (basisLift i : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  fin_cases i
  · exact IsSymmetric.one
  · exact liftA_isSymmetric
  · exact (isSymmetric_pow liftA_isSymmetric 2).add liftB_isSymmetric
  · exact liftA_isSymmetric.mul liftB_isSymmetric
  · exact (isSymmetric_pow liftA_isSymmetric 3).add liftC_isSymmetric
  · exact liftA_isSymmetric.mul liftCplus_isSymmetric
  · exact (isSymmetric_pow liftA_isSymmetric 3).mul
      ((isSymmetric_pow liftA_isSymmetric 2).add liftB_isSymmetric)
  · exact (((isSymmetric_pow liftA_isSymmetric 6).add
      ((isSymmetric_pow liftA_isSymmetric 3).mul liftC_isSymmetric)).add
      (isSymmetric_pow liftB_isSymmetric 3)).add (isSymmetric_pow liftC_isSymmetric 2)

/-- Symmetric lift of `generator j`. -/
noncomputable def genLiftSym (j : Fin 8) : MvPolynomial (Fin 3) ℤ := liftA * liftCplus * basisLift j

/-- Alternating lift of `generator j` (replace the symmetric factor `liftCplus` by the
alternating `liftDelta`, since both reduce to `cplus`). -/
noncomputable def genLiftAlt (j : Fin 8) : MvPolynomial (Fin 3) ℤ := liftA * liftDelta * basisLift j

theorem reduceTwo_genLiftSym (j : Fin 8) : reduceTwo (genLiftSym j) = generator j := by
  show reduceTwo (liftA * liftCplus * basisLift j) = generator j
  rw [map_mul, map_mul, reduceTwo_liftA, reduceTwo_liftCplus, reduceTwo_basisLift]
  rfl

theorem reduceTwo_genLiftAlt (j : Fin 8) : reduceTwo (genLiftAlt j) = generator j := by
  show reduceTwo (liftA * liftDelta * basisLift j) = generator j
  rw [map_mul, map_mul, reduceTwo_liftA, reduceTwo_liftDelta, reduceTwo_basisLift]
  rfl

theorem genLiftSym_isSymmetric (j : Fin 8) : (genLiftSym j).IsSymmetric :=
  (liftA_isSymmetric.mul liftCplus_isSymmetric).mul (basisLift_isSymmetric j)

theorem genLiftAlt_isAlternating (j : Fin 8) : IsAlternating (genLiftAlt j) :=
  alternating_mul_symmetric (symmetric_mul_alternating liftA_isSymmetric liftDelta_isAlternating)
    (basisLift_isSymmetric j)

/-- Symmetric lift of the odd generator `oddGenerator j = generator j * d7 ^ kappa j`. -/
noncomputable def oddGenLiftSym (j : Fin 8) : MvPolynomial (Fin 3) ℤ := genLiftSym j * liftD7 ^ kappa j

/-- Alternating lift of `oddGenerator j`. -/
noncomputable def oddGenLiftAlt (j : Fin 8) : MvPolynomial (Fin 3) ℤ := genLiftAlt j * liftD7 ^ kappa j

theorem reduceTwo_oddGenLiftSym (j : Fin 8) : reduceTwo (oddGenLiftSym j) = oddGenerator j := by
  show reduceTwo (genLiftSym j * liftD7 ^ kappa j) = oddGenerator j
  rw [map_mul, map_pow, reduceTwo_genLiftSym, reduceTwo_liftD7]
  rfl

theorem reduceTwo_oddGenLiftAlt (j : Fin 8) : reduceTwo (oddGenLiftAlt j) = oddGenerator j := by
  show reduceTwo (genLiftAlt j * liftD7 ^ kappa j) = oddGenerator j
  rw [map_mul, map_pow, reduceTwo_genLiftAlt, reduceTwo_liftD7]
  rfl

theorem oddGenLiftSym_isSymmetric (j : Fin 8) : (oddGenLiftSym j).IsSymmetric :=
  (genLiftSym_isSymmetric j).mul (isSymmetric_pow liftD7_isSymmetric (kappa j))

theorem oddGenLiftAlt_isAlternating (j : Fin 8) : IsAlternating (oddGenLiftAlt j) :=
  alternating_mul_symmetric (genLiftAlt_isAlternating j) (isSymmetric_pow liftD7_isSymmetric (kappa j))

private theorem invariantGens_isSymmetric :
    ∀ i, (![liftD4, liftD6, liftD7 ^ 2] i : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  intro i
  fin_cases i
  · exact liftD4_isSymmetric
  · exact liftD6_isSymmetric
  · exact isSymmetric_pow liftD7_isSymmetric 2

private theorem invariantVec_reduceTwo :
    (fun i => reduceTwo (![liftD4, liftD6, liftD7 ^ 2] i))
      = (![d4, d6, d7 ^ 2] : Fin 3 → Poly2) := by
  funext i
  fin_cases i <;> simp [map_pow, reduceTwo_liftD4, reduceTwo_liftD6, reduceTwo_liftD7]

/-- An arbitrary (non-canonical) symmetric integral lift of `evalR0 (r j)`, built by lifting
`r j` to some integral polynomial and feeding it through `D4, D6, D7²`; automatically symmetric
regardless of the chosen lift of `r j`. -/
noncomputable def coeffLiftOf (r : Fin 8 → Poly2) (j : Fin 8) : MvPolynomial (Fin 3) ℤ :=
  bind₁ ![liftD4, liftD6, liftD7 ^ 2] (exists_lift (r j)).choose

theorem coeffLiftOf_isSymmetric (r : Fin 8 → Poly2) (j : Fin 8) :
    (coeffLiftOf r j).IsSymmetric :=
  bind₁_isSymmetric_of_symmetric invariantGens_isSymmetric _

theorem reduceTwo_coeffLiftOf (r : Fin 8 → Poly2) (j : Fin 8) :
    reduceTwo (coeffLiftOf r j) = evalR0 (r j) := by
  show reduceTwo (bind₁ ![liftD4, liftD6, liftD7 ^ 2] (exists_lift (r j)).choose) = evalR0 (r j)
  rw [MvPolynomial.map_bind₁, invariantVec_reduceTwo, (exists_lift (r j)).choose_spec]
  rfl

/-- The explicit symmetric integral lift of `expandOdd r`. -/
noncomputable def liftSym (r : Fin 8 → Poly2) : MvPolynomial (Fin 3) ℤ :=
  ∑ j, coeffLiftOf r j * oddGenLiftSym j

/-- The explicit alternating integral lift of `expandOdd r`. -/
noncomputable def liftAlt (r : Fin 8 → Poly2) : MvPolynomial (Fin 3) ℤ :=
  ∑ j, coeffLiftOf r j * oddGenLiftAlt j

theorem liftSym_isSymmetric (r : Fin 8 → Poly2) : (liftSym r).IsSymmetric :=
  isSymmetric_sum Finset.univ _
    (fun j _ => (coeffLiftOf_isSymmetric r j).mul (oddGenLiftSym_isSymmetric j))

theorem liftAlt_isAlternating (r : Fin 8 → Poly2) : IsAlternating (liftAlt r) :=
  isAlternating_sum Finset.univ _
    (fun j _ => symmetric_mul_alternating (coeffLiftOf_isSymmetric r j)
      (oddGenLiftAlt_isAlternating j))

theorem reduceTwo_liftSym (r : Fin 8 → Poly2) : reduceTwo (liftSym r) = expandOdd r := by
  show reduceTwo (∑ j, coeffLiftOf r j * oddGenLiftSym j) = expandOdd r
  show reduceTwo (∑ j, coeffLiftOf r j * oddGenLiftSym j)
      = ∑ j, evalR0 (r j) * oddGenerator j
  rw [map_sum]
  exact Finset.sum_congr rfl
    (fun j _ => by rw [map_mul, reduceTwo_coeffLiftOf, reduceTwo_oddGenLiftSym])

theorem reduceTwo_liftAlt (r : Fin 8 → Poly2) : reduceTwo (liftAlt r) = expandOdd r := by
  show reduceTwo (∑ j, coeffLiftOf r j * oddGenLiftAlt j)
      = ∑ j, evalR0 (r j) * oddGenerator j
  rw [map_sum]
  exact Finset.sum_congr rfl
    (fun j _ => by rw [map_mul, reduceTwo_coeffLiftOf, reduceTwo_oddGenLiftAlt])

theorem liftSym_even_norm (r : Fin 8 → Poly2) :
    ∃ g : MvPolynomial (Fin 3) ℤ, threeTermNorm (liftSym r) = C 2 * g :=
  exists_half (by rw [reduceTwo_threeTermNorm, reduceTwo_liftSym]; exact expandOdd_norm_zero r)

theorem liftAlt_even_norm (r : Fin 8 → Poly2) :
    ∃ g : MvPolynomial (Fin 3) ℤ, threeTermNorm (liftAlt r) = C 2 * g :=
  exists_half (by rw [reduceTwo_threeTermNorm, reduceTwo_liftAlt]; exact expandOdd_norm_zero r)

/-- **Lemma 5.5, clause 1** (existence of symmetric/alternating integral lifts with even
norm). -/
theorem lemma_5_5_clause1 :
    ∀ r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2),
      (∃ v g : MvPolynomial (Fin 3) ℤ, v.IsSymmetric ∧ reduceTwo v = expandOdd r ∧
        threeTermNorm v = C 2 * g) ∧
      (∃ v g : MvPolynomial (Fin 3) ℤ, IsAlternating v ∧ reduceTwo v = expandOdd r ∧
        threeTermNorm v = C 2 * g) := by
  intro r
  obtain ⟨g1, hg1⟩ := liftSym_even_norm r
  obtain ⟨g2, hg2⟩ := liftAlt_even_norm r
  exact ⟨⟨liftSym r, g1, liftSym_isSymmetric r, reduceTwo_liftSym r, hg1⟩,
         ⟨liftAlt r, g2, liftAlt_isAlternating r, reduceTwo_liftAlt r, hg2⟩⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
