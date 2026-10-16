module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.Operators
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.SquaredLiftInvariance
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.OperatorAdditivity

@[expose] public section



/-!
# Generic Leibniz-defect assembly for `β`

The engine that turns `leibniz_step` + the mod-two defect operators `delta_p`, `delta_q`
(from `DeltaOperators.lean`) into the three "multiply the base case by a Dickson lift"
steps of the `W(j,m)` table: multiplying `v` by `liftD4`, `liftD6`, or `liftD4 * liftD6`
changes `β(v)` by `d4 * β(v) + delta_p(w)`, `d6 * β(v) + delta_q(w)`, or
`d4*d6*β(v) + d4*delta_q(w) + d6*delta_p(w)` respectively, where `w = reduceTwo v`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem fixed_d4 : ∀ t ∈ piSubstitutions, bind₁ t d4 = d4 :=
  fun t ht => by simpa [invariant] using piSubstitutions_invariant t ht 0

private theorem fixed_d6 : ∀ t ∈ piSubstitutions, bind₁ t d6 = d6 :=
  fun t ht => by simpa [invariant] using piSubstitutions_invariant t ht 1

private theorem fixed_d4_mul_d6 : ∀ t ∈ piSubstitutions, bind₁ t (d4 * d6) = d4 * d6 :=
  fun t ht => by rw [map_mul, fixed_d4 t ht, fixed_d6 t ht]

/-- The generic Leibniz-defect assembly: multiplying by an integral Dickson lift `D`
with known defects `E1, E2` changes `β` by `Dbar * β(v) + δ(reduceTwo v)`, where `δ`
is the mod-two defect built from `E1, E2`. -/
theorem beta_mul_generic {D E1 E2 : MvPolynomial (Fin 3) ℤ} {Dbar : Poly2}
    (h1 : bind₁ A1vec D = D + C 2 * E1) (h2 : bind₁ A2vec D = D + C 2 * E2)
    (hDbar : reduceTwo D = Dbar) (hfix : ∀ t ∈ piSubstitutions, bind₁ t Dbar = Dbar)
    {v g : MvPolynomial (Fin 3) ℤ} (hg : threeTermNorm v = C 2 * g) :
    threeTermNorm (D * v) = C 2 * (D * g + E1 * bind₁ A1vec v + E2 * bind₁ A2vec v) ∧
    piOperator (reduceTwo (D * g + E1 * bind₁ A1vec v + E2 * bind₁ A2vec v))
      = Dbar * piOperator (reduceTwo g)
        + piOperator (reduceTwo E1 * sub₁ (reduceTwo v) + reduceTwo E2 * sub₂ (reduceTwo v)) := by
  refine ⟨leibniz_step h1 h2 hg, ?_⟩
  have key : piOperator (reduceTwo (D * g + E1 * bind₁ A1vec v + E2 * bind₁ A2vec v))
      = piOperator (reduceTwo (D * g)) + piOperator (reduceTwo (E1 * bind₁ A1vec v))
        + piOperator (reduceTwo (E2 * bind₁ A2vec v)) := by
    simp only [map_add, piOperator_add]
  rw [key, map_mul, map_mul, map_mul, hDbar, reduceTwo_bind1_A1vec, reduceTwo_bind1_A2vec,
      piOperator_mul_of_fixed hfix, piOperator_add]
  ring

/-- Multiplying by `liftD4` changes `β` by `d4 * β(v) + delta_p(reduceTwo v)`. -/
theorem beta_mul_D4 {v g : MvPolynomial (Fin 3) ℤ} (hg : threeTermNorm v = C 2 * g) :
    threeTermNorm (liftD4 * v)
      = C 2 * (liftD4 * g + E1_D4 * bind₁ A1vec v + E2_D4 * bind₁ A2vec v) ∧
    piOperator (reduceTwo (liftD4 * g + E1_D4 * bind₁ A1vec v + E2_D4 * bind₁ A2vec v))
      = d4 * piOperator (reduceTwo g) + delta_p (reduceTwo v) :=
  beta_mul_generic h1_D4 h2_D4 reduceTwo_liftD4 fixed_d4 hg

/-- Multiplying by `liftD6` changes `β` by `d6 * β(v) + delta_q(reduceTwo v)`. -/
theorem beta_mul_D6 {v g : MvPolynomial (Fin 3) ℤ} (hg : threeTermNorm v = C 2 * g) :
    threeTermNorm (liftD6 * v)
      = C 2 * (liftD6 * g + E1_D6 * bind₁ A1vec v + E2_D6 * bind₁ A2vec v) ∧
    piOperator (reduceTwo (liftD6 * g + E1_D6 * bind₁ A1vec v + E2_D6 * bind₁ A2vec v))
      = d6 * piOperator (reduceTwo g) + delta_q (reduceTwo v) :=
  beta_mul_generic h1_D6 h2_D6 reduceTwo_liftD6 fixed_d6 hg

noncomputable def E1_D4D6 : MvPolynomial (Fin 3) ℤ :=
  liftD4 * E1_D6 + liftD6 * E1_D4 + C 2 * E1_D4 * E1_D6

noncomputable def E2_D4D6 : MvPolynomial (Fin 3) ℤ :=
  liftD4 * E2_D6 + liftD6 * E2_D4 + C 2 * E2_D4 * E2_D6

theorem h1_D4D6 : bind₁ A1vec (liftD4 * liftD6) = liftD4 * liftD6 + C 2 * E1_D4D6 := by
  simp only [map_mul, h1_D4, h1_D6, E1_D4D6]
  ring

theorem h2_D4D6 : bind₁ A2vec (liftD4 * liftD6) = liftD4 * liftD6 + C 2 * E2_D4D6 := by
  simp only [map_mul, h2_D4, h2_D6, E2_D4D6]
  ring

private theorem reduceTwo_D4D6 : reduceTwo (liftD4 * liftD6) = d4 * d6 := by
  rw [map_mul, reduceTwo_liftD4, reduceTwo_liftD6]

private theorem reduceTwo_E1_D4D6 : reduceTwo E1_D4D6 = d4 * Ebar1_D6 + d6 * Ebar1_D4 := by
  have heq : E1_D4D6 = liftD4 * E1_D6 + liftD6 * E1_D4 + C 2 * (E1_D4 * E1_D6) := by
    simp only [E1_D4D6]; ring
  rw [heq, map_add, map_add, reduceTwo_two_mul, add_zero, map_mul, map_mul,
    reduceTwo_liftD4, reduceTwo_liftD6]
  simp only [Ebar1_D4, Ebar1_D6]

private theorem reduceTwo_E2_D4D6 : reduceTwo E2_D4D6 = d4 * Ebar2_D6 + d6 * Ebar2_D4 := by
  have heq : E2_D4D6 = liftD4 * E2_D6 + liftD6 * E2_D4 + C 2 * (E2_D4 * E2_D6) := by
    simp only [E2_D4D6]; ring
  rw [heq, map_add, map_add, reduceTwo_two_mul, add_zero, map_mul, map_mul,
    reduceTwo_liftD4, reduceTwo_liftD6]
  simp only [Ebar2_D4, Ebar2_D6]

/-- Multiplying by `liftD4 * liftD6` changes `β` by
`d4*d6 * β(v) + d4 * delta_q(reduceTwo v) + d6 * delta_p(reduceTwo v)`. -/
theorem beta_mul_D4D6 {v g : MvPolynomial (Fin 3) ℤ} (hg : threeTermNorm v = C 2 * g) :
    threeTermNorm (liftD4 * liftD6 * v)
      = C 2 * (liftD4 * liftD6 * g + E1_D4D6 * bind₁ A1vec v + E2_D4D6 * bind₁ A2vec v) ∧
    piOperator (reduceTwo (liftD4 * liftD6 * g + E1_D4D6 * bind₁ A1vec v + E2_D4D6 * bind₁ A2vec v))
      = d4 * d6 * piOperator (reduceTwo g)
        + d4 * delta_q (reduceTwo v) + d6 * delta_p (reduceTwo v) := by
  obtain ⟨hnorm, hpi⟩ := beta_mul_generic h1_D4D6 h2_D4D6 reduceTwo_D4D6 fixed_d4_mul_d6 hg
  refine ⟨hnorm, ?_⟩
  rw [hpi, reduceTwo_E1_D4D6, reduceTwo_E2_D4D6]
  have expand : (d4 * Ebar1_D6 + d6 * Ebar1_D4) * sub₁ (reduceTwo v)
      + (d4 * Ebar2_D6 + d6 * Ebar2_D4) * sub₂ (reduceTwo v)
      = d4 * (Ebar1_D6 * sub₁ (reduceTwo v) + Ebar2_D6 * sub₂ (reduceTwo v))
        + d6 * (Ebar1_D4 * sub₁ (reduceTwo v) + Ebar2_D4 * sub₂ (reduceTwo v)) := by
    ring
  rw [expand, piOperator_add, piOperator_mul_of_fixed fixed_d4, piOperator_mul_of_fixed fixed_d6]
  show d4 * d6 * piOperator (reduceTwo g) + (d4 * piOperator (Ebar1_D6 * sub₁ (reduceTwo v) + Ebar2_D6 * sub₂ (reduceTwo v))
      + d6 * piOperator (Ebar1_D4 * sub₁ (reduceTwo v) + Ebar2_D4 * sub₂ (reduceTwo v)))
      = d4 * d6 * piOperator (reduceTwo g) + d4 * delta_q (reduceTwo v) + d6 * delta_p (reduceTwo v)
  rw [delta_p, delta_q]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
