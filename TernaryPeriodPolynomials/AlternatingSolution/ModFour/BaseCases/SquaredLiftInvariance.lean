module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Basics
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.DicksonInvariance18

@[expose] public section



/-!
# Mod-four invariance of `evalSquaredLift` (Lemma 5.5 clause 4: R₂-linearity)

`liftD4, liftD6, liftD7` reduce mod two to `d4, d6, d7`, which `sub₁ = bind₁![X1,X0+X1,X2]`
and `sub₂ = bind₁![X0+X1,X0,X2]` fix (`TernaryPoly.CharTwoNorm.sub₁_invariant/sub₂_invariant`).
Since `sub₁, sub₂` are exactly the mod-two reductions of `threeTermNorm`'s two integral
substitutions, this gives mod-two invariance of `liftD4, liftD6, liftD7`, hence mod-four
invariance of their squares, hence (by an induction on `P`) of `evalSquaredLift P` for every
integral `P`. Combined with `piSubstitutions_invariantSq_fixed`, this gives clause 4 of
Lemma 5.5.
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (d4 d6 d7 sub₁ sub₂ sub₁_invariant sub₂_invariant invariant)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- `reduceTwo` sends the first `threeTermNorm` substitution vector to `sub₁`'s. -/
private theorem A1_reduceTwo_eq :
    (fun i => MvPolynomial.map (Int.castRingHom (ZMod 2))
        (![(-X 1 : MvPolynomial (Fin 3) ℤ), X 0 - X 1, X 2] i))
      = (![X 1, X 0 + X 1, X 2] : Fin 3 → Poly2) := by
  funext i
  fin_cases i <;> simp [sub_eq_add_neg, CharTwo.neg_eq]

/-- `reduceTwo` sends the second `threeTermNorm` substitution vector to `sub₂`'s. -/
private theorem A2_reduceTwo_eq :
    (fun i => MvPolynomial.map (Int.castRingHom (ZMod 2))
        (![(X 1 - X 0 : MvPolynomial (Fin 3) ℤ), -X 0, X 2] i))
      = (![X 0 + X 1, X 0, X 2] : Fin 3 → Poly2) := by
  funext i
  fin_cases i
  · simp [sub_eq_add_neg, CharTwo.neg_eq]
    ring
  · simp [sub_eq_add_neg, CharTwo.neg_eq]
  · simp

/-- Reduction mod two commutes with the first `threeTermNorm` substitution and `sub₁`. -/
private theorem reduceTwo_bind₁_A1 (f : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (bind₁ ![-X 1, X 0 - X 1, X 2] f) = sub₁ (reduceTwo f) := by
  show MvPolynomial.map (Int.castRingHom (ZMod 2)) (bind₁ ![-X 1, X 0 - X 1, X 2] f)
      = sub₁ (MvPolynomial.map (Int.castRingHom (ZMod 2)) f)
  simp only [sub₁, MvPolynomial.map_bind₁, A1_reduceTwo_eq]

/-- Reduction mod two commutes with the second `threeTermNorm` substitution and `sub₂`. -/
private theorem reduceTwo_bind₁_A2 (f : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (bind₁ ![X 1 - X 0, -X 0, X 2] f) = sub₂ (reduceTwo f) := by
  show MvPolynomial.map (Int.castRingHom (ZMod 2)) (bind₁ ![X 1 - X 0, -X 0, X 2] f)
      = sub₂ (MvPolynomial.map (Int.castRingHom (ZMod 2)) f)
  simp only [sub₂, MvPolynomial.map_bind₁, A2_reduceTwo_eq]

private theorem sub₁_fixes_d4 : sub₁ d4 = d4 := by simpa [invariant] using sub₁_invariant 0
private theorem sub₁_fixes_d6 : sub₁ d6 = d6 := by simpa [invariant] using sub₁_invariant 1
private theorem sub₁_fixes_d7 : sub₁ d7 = d7 := by simpa [invariant] using sub₁_invariant 2
private theorem sub₂_fixes_d4 : sub₂ d4 = d4 := by simpa [invariant] using sub₂_invariant 0
private theorem sub₂_fixes_d6 : sub₂ d6 = d6 := by simpa [invariant] using sub₂_invariant 1
private theorem sub₂_fixes_d7 : sub₂ d7 = d7 := by simpa [invariant] using sub₂_invariant 2

/-- `D` is invariant mod two under the first `threeTermNorm` substitution, given its
reduction is fixed by `sub₁`. -/
private theorem mod_two_inv_A1 {D : MvPolynomial (Fin 3) ℤ} {d : Poly2} (hd : reduceTwo D = d)
    (hfix : sub₁ d = d) : reduceTwo (bind₁ ![-X 1, X 0 - X 1, X 2] D) = reduceTwo D := by
  rw [reduceTwo_bind₁_A1, hd, hfix]

private theorem mod_two_inv_A2 {D : MvPolynomial (Fin 3) ℤ} {d : Poly2} (hd : reduceTwo D = d)
    (hfix : sub₂ d = d) : reduceTwo (bind₁ ![X 1 - X 0, -X 0, X 2] D) = reduceTwo D := by
  rw [reduceTwo_bind₁_A2, hd, hfix]

/-- If `D` is invariant mod two under a substitution `A`, then `D²` is invariant mod four. -/
private theorem sq_mod_four_of_mod_two {A : Fin 3 → MvPolynomial (Fin 3) ℤ}
    {D : MvPolynomial (Fin 3) ℤ} (h : reduceTwo (bind₁ A D) = reduceTwo D) :
    ∃ e : MvPolynomial (Fin 3) ℤ, bind₁ A (D ^ 2) = D ^ 2 + 4 * e := by
  have h0 : reduceTwo (bind₁ A D - D) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨e, he⟩ := exists_half h0
  have hc2 : (C 2 : MvPolynomial (Fin 3) ℤ) = 2 := map_ofNat C 2
  rw [hc2] at he
  have hAD : bind₁ A D = D + 2 * e := by rw [sub_eq_iff_eq_add.mp he]; ring
  refine ⟨e * D + e ^ 2, ?_⟩
  have hsq : bind₁ A (D ^ 2) = (bind₁ A D) ^ 2 := map_pow _ _ _
  rw [hsq, hAD]; ring

private theorem mod_four_D4_A1 :
    ∃ e, bind₁ ![-X 1, X 0 - X 1, X 2] (liftD4 ^ 2) = liftD4 ^ 2 + 4 * e :=
  sq_mod_four_of_mod_two (mod_two_inv_A1 reduceTwo_liftD4 sub₁_fixes_d4)

private theorem mod_four_D6_A1 :
    ∃ e, bind₁ ![-X 1, X 0 - X 1, X 2] (liftD6 ^ 2) = liftD6 ^ 2 + 4 * e :=
  sq_mod_four_of_mod_two (mod_two_inv_A1 reduceTwo_liftD6 sub₁_fixes_d6)

private theorem mod_four_D7_A1 :
    ∃ e, bind₁ ![-X 1, X 0 - X 1, X 2] (liftD7 ^ 2) = liftD7 ^ 2 + 4 * e :=
  sq_mod_four_of_mod_two (mod_two_inv_A1 reduceTwo_liftD7 sub₁_fixes_d7)

private theorem mod_four_D4_A2 :
    ∃ e, bind₁ ![X 1 - X 0, -X 0, X 2] (liftD4 ^ 2) = liftD4 ^ 2 + 4 * e :=
  sq_mod_four_of_mod_two (mod_two_inv_A2 reduceTwo_liftD4 sub₂_fixes_d4)

private theorem mod_four_D6_A2 :
    ∃ e, bind₁ ![X 1 - X 0, -X 0, X 2] (liftD6 ^ 2) = liftD6 ^ 2 + 4 * e :=
  sq_mod_four_of_mod_two (mod_two_inv_A2 reduceTwo_liftD6 sub₂_fixes_d6)

private theorem mod_four_D7_A2 :
    ∃ e, bind₁ ![X 1 - X 0, -X 0, X 2] (liftD7 ^ 2) = liftD7 ^ 2 + 4 * e :=
  sq_mod_four_of_mod_two (mod_two_inv_A2 reduceTwo_liftD7 sub₂_fixes_d7)

private theorem mod_four_gen_A1 :
    ∀ i : Fin 3, ∃ e, bind₁ ![-X 1, X 0 - X 1, X 2] (![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i)
        = ![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i + 4 * e := by
  intro i
  fin_cases i
  · simpa using mod_four_D4_A1
  · simpa using mod_four_D6_A1
  · simpa using mod_four_D7_A1

private theorem mod_four_gen_A2 :
    ∀ i : Fin 3, ∃ e, bind₁ ![X 1 - X 0, -X 0, X 2] (![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i)
        = ![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i + 4 * e := by
  intro i
  fin_cases i
  · simpa using mod_four_D4_A2
  · simpa using mod_four_D6_A2
  · simpa using mod_four_D7_A2

/-- If the three generators `![D4²,D6²,D7²] i` are each invariant mod four under `A`, then so
is `evalSquaredLift P` for every integral `P`. -/
private theorem mod_four_gen {A : Fin 3 → MvPolynomial (Fin 3) ℤ}
    (hgen : ∀ i : Fin 3, ∃ e, bind₁ A (![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i)
        = ![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i + 4 * e) :
    ∀ P : MvPolynomial (Fin 3) ℤ,
      ∃ e, bind₁ A (evalSquaredLift P) = evalSquaredLift P + 4 * e := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [evalSquaredLift]⟩
  | add p q hp hq =>
    obtain ⟨ep, hep⟩ := hp
    obtain ⟨eqq, heq⟩ := hq
    refine ⟨ep + eqq, ?_⟩
    have h1 : evalSquaredLift (p + q) = evalSquaredLift p + evalSquaredLift q := map_add _ _ _
    have h2 : bind₁ A (evalSquaredLift (p + q))
        = bind₁ A (evalSquaredLift p) + bind₁ A (evalSquaredLift q) := by rw [h1, map_add]
    rw [h2, h1, hep, heq]; ring
  | mul_X p i hp =>
    obtain ⟨ep, hep⟩ := hp
    obtain ⟨ei, hei⟩ := hgen i
    have hXi : evalSquaredLift (X i) = ![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i := bind₁_X_right _ i
    have hmul : evalSquaredLift (p * X i) = evalSquaredLift p * evalSquaredLift (X i) :=
      map_mul _ _ _
    have hbind : bind₁ A (evalSquaredLift (p * X i))
        = (evalSquaredLift p + 4 * ep) * (![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i + 4 * ei) := by
      rw [hmul, map_mul, hXi, hep, hei]
    refine ⟨ep * (![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i) + evalSquaredLift p * ei
        + 4 * ep * ei, ?_⟩
    rw [hbind, hmul, hXi]
    ring

theorem mod_four_evalSquaredLift_A1 (P : MvPolynomial (Fin 3) ℤ) :
    ∃ e, bind₁ ![-X 1, X 0 - X 1, X 2] (evalSquaredLift P) = evalSquaredLift P + 4 * e :=
  mod_four_gen mod_four_gen_A1 P

theorem mod_four_evalSquaredLift_A2 (P : MvPolynomial (Fin 3) ℤ) :
    ∃ e, bind₁ ![X 1 - X 0, -X 0, X 2] (evalSquaredLift P) = evalSquaredLift P + 4 * e :=
  mod_four_gen mod_four_gen_A2 P

/-- `reduceTwo (evalSquaredLift P) = bind₁ ![d4^2,d6^2,d7^2] (reduceTwo P)`. -/
theorem reduceTwo_evalSquaredLift (P : MvPolynomial (Fin 3) ℤ) :
    reduceTwo (evalSquaredLift P) = bind₁ ![d4 ^ 2, d6 ^ 2, d7 ^ 2] (reduceTwo P) := by
  have h := MvPolynomial.map_bind₁ (Int.castRingHom (ZMod 2))
    (![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] : Fin 3 → MvPolynomial (Fin 3) ℤ) P
  have hvec : (fun i => reduceTwo (![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2] i))
      = (![d4 ^ 2, d6 ^ 2, d7 ^ 2] : Fin 3 → Poly2) := by
    funext i
    fin_cases i <;> simp [map_pow, reduceTwo_liftD4, reduceTwo_liftD6, reduceTwo_liftD7]
  rw [hvec] at h
  exact h

/-- `reduceTwo (evalSquaredLift P)` is fixed by every `piOperator` substitution. -/
theorem evalSquaredLift_pi_fixed (P : MvPolynomial (Fin 3) ℤ) {t : Fin 3 → Poly2}
    (ht : t ∈ piSubstitutions) :
    bind₁ t (reduceTwo (evalSquaredLift P)) = reduceTwo (evalSquaredLift P) := by
  rw [reduceTwo_evalSquaredLift]
  exact piSubstitutions_invariantSq_fixed ht (reduceTwo P)

private theorem list_sum_map_mul_const {l : List (Fin 3 → Poly2)} {Q h : Poly2}
    (hQ : ∀ t ∈ l, bind₁ t Q = Q) :
    (l.map fun t => bind₁ t (Q * h)).sum = Q * (l.map fun t => bind₁ t h).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.mem_cons] at *
    rw [map_mul, hQ t (Or.inl rfl), ih (fun t' ht' => hQ t' (Or.inr ht'))]
    ring

/-- `piOperator` factors out a `piOperator`-fixed polynomial. -/
theorem piOperator_mul_of_fixed {Q h : Poly2} (hQ : ∀ t ∈ piSubstitutions, bind₁ t Q = Q) :
    piOperator (Q * h) = Q * piOperator h := by
  simp only [piOperator]
  exact list_sum_map_mul_const hQ

/-- **Lemma 5.5, clause 4** (R₂-linearity of `β`). -/
theorem lemma_5_5_clause4 :
    ∀ P v g g' : MvPolynomial (Fin 3) ℤ, threeTermNorm v = C 2 * g →
      threeTermNorm (evalSquaredLift P * v) = C 2 * g' →
      piOperator (reduceTwo g') = reduceTwo (evalSquaredLift P) * piOperator (reduceTwo g) := by
  intro P v g g' hv hPv
  have hc2 : (C 2 : MvPolynomial (Fin 3) ℤ) = 2 := map_ofNat C 2
  rw [hc2] at hv hPv
  obtain ⟨e1, he1⟩ := mod_four_evalSquaredLift_A1 P
  obtain ⟨e2, he2⟩ := mod_four_evalSquaredLift_A2 P
  have hexpand : threeTermNorm (evalSquaredLift P * v)
      = evalSquaredLift P * threeTermNorm v
        + 4 * (e1 * bind₁ ![-X 1, X 0 - X 1, X 2] v + e2 * bind₁ ![X 1 - X 0, -X 0, X 2] v) := by
    simp only [threeTermNorm, map_mul]
    rw [he1, he2]
    ring
  rw [hv, hPv] at hexpand
  have h2ne : (2 : MvPolynomial (Fin 3) ℤ) ≠ 0 := by
    intro hz
    rw [← hc2, MvPolynomial.C_eq_zero] at hz
    norm_num at hz
  have hcancel : g' = evalSquaredLift P * g
      + 2 * (e1 * bind₁ ![-X 1, X 0 - X 1, X 2] v + e2 * bind₁ ![X 1 - X 0, -X 0, X 2] v) := by
    apply mul_left_cancel₀ h2ne
    rw [hexpand]; ring
  have hreduce2 : reduceTwo (2 * (e1 * bind₁ ![-X 1, X 0 - X 1, X 2] v
      + e2 * bind₁ ![X 1 - X 0, -X 0, X 2] v) : MvPolynomial (Fin 3) ℤ) = 0 := by
    rw [← hc2]; exact reduceTwo_two_mul _
  rw [hcancel, map_add, map_mul, hreduce2, add_zero]
  exact piOperator_mul_of_fixed (fun t ht => evalSquaredLift_pi_fixed P ht)

end TernaryPeriodPolynomials.Argument.ModFourBeta
