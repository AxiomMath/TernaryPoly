module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.DicksonDefects

@[expose] public section



/-!
# The Leibniz-defect operators `δ_p`, `δ_q`

Naturality of `reduceTwo` under the two `threeTermNorm` substitutions, and the
mod-two defect operators `delta_p`, `delta_q` built from the integral defects of
`liftD4`, `liftD6` computed in `DicksonDefects.lean`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem reduceTwo_A1vec_eq :
    (fun i => reduceTwo (A1vec i)) = (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) := by
  funext i
  fin_cases i <;> simp [A1vec, sub_eq_add_neg, CharTwo.neg_eq]

private theorem reduceTwo_A2vec_eq :
    (fun i => reduceTwo (A2vec i)) = (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) := by
  funext i
  fin_cases i
  · simp [A2vec, sub_eq_add_neg, CharTwo.neg_eq]
    ring
  · simp [A2vec, sub_eq_add_neg, CharTwo.neg_eq]
  · simp [A2vec, sub_eq_add_neg]

/-- `reduceTwo` commutes with the first `threeTermNorm` substitution, matching `sub₁`. -/
theorem reduceTwo_bind1_A1vec (v : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (bind₁ A1vec v) = sub₁ (reduceTwo v) := by
  show MvPolynomial.map (Int.castRingHom (ZMod 2)) (bind₁ A1vec v)
      = sub₁ (MvPolynomial.map (Int.castRingHom (ZMod 2)) v)
  rw [MvPolynomial.map_bind₁, reduceTwo_A1vec_eq]
  rfl

/-- `reduceTwo` commutes with the second `threeTermNorm` substitution, matching `sub₂`. -/
theorem reduceTwo_bind1_A2vec (v : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (bind₁ A2vec v) = sub₂ (reduceTwo v) := by
  show MvPolynomial.map (Int.castRingHom (ZMod 2)) (bind₁ A2vec v)
      = sub₂ (MvPolynomial.map (Int.castRingHom (ZMod 2)) v)
  rw [MvPolynomial.map_bind₁, reduceTwo_A2vec_eq]
  rfl

noncomputable def Ebar1_D4 : Poly2 := reduceTwo E1_D4
noncomputable def Ebar2_D4 : Poly2 := reduceTwo E2_D4
noncomputable def Ebar1_D6 : Poly2 := reduceTwo E1_D6
noncomputable def Ebar2_D6 : Poly2 := reduceTwo E2_D6

/-- The `D4`-side first-order Leibniz defect of `β`, as a mod-two operator on `w = reduceTwo v`. -/
noncomputable def delta_p (w : Poly2) : Poly2 :=
  piOperator (Ebar1_D4 * sub₁ w + Ebar2_D4 * sub₂ w)

/-- The `D6`-side first-order Leibniz defect of `β`, as a mod-two operator on `w = reduceTwo v`. -/
noncomputable def delta_q (w : Poly2) : Poly2 :=
  piOperator (Ebar1_D6 * sub₁ w + Ebar2_D6 * sub₂ w)

end TernaryPeriodPolynomials.Argument.ModFourBeta
