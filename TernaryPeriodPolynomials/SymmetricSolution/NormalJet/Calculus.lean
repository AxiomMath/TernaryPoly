module

public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Line
public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Operators

@[expose] public section


/-!
# The calculus behind the `Z`-derivative of `J_v` on the normal line `Z = 3Y` (MR-7, second identity)

Formalized by Claude Sonnet 5.5.  Proof of Lemma `lem:period-extraction`.

Polynomial-level ingredients: the chain rule for substitutions, commutation of partial derivatives, the product rule for the Bernoulli operator `B(-t∂_X)` in the third variable
(`pderiv_two_bernoulliOperator`, with the parameter derivative `bernoulliParam` = `∑ b_r (-r)(-t)^(r-1) ∂ʳ`), the frame computations
`ψ₁ⁱ`, `ψ₂ⁱ` at `Z = 3Y` (`psi1_at_three`, `dpsi1_at_three`, `dpsi2a_at_three`, `dpsi2b_at_three`: oddness and the transposition `(1 3)` of the symmetry), `h_X = v₂ - v₃`
(`pderiv_zero_hFrame`), and the assembled expression `bind_sigma3_pderiv_two_obstruction` for `∂_Z J_v |_{Z=3Y}` before the operator algebra.
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.NormalJet

open TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers (polynomialValue polynomialValue_bind)

section Calculus

/-- Partial derivatives of a polynomial commute. -/
theorem pderiv_comm_poly (i j : Fin 3) (q : Poly) :
    pderiv i (pderiv j q) = pderiv j (pderiv i q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp]
    have h1 : ∀ a b : Fin 3, pderiv a (X b : Poly) = if a = b then 1 else 0 := by
      intro a b
      by_cases h : a = b
      · simp [h]
      · simp [h]
    simp only [h1]
    split_ifs <;> simp <;> ring

theorem pderiv_iterate_comm (j : Fin 3) (r : ℕ) (q : Poly) :
    pderiv j (((fun x : Poly => pderiv 0 x)^[r]) q) = ((fun x : Poly => pderiv 0 x)^[r]) (pderiv j q) := by
  induction r generalizing q with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, pderiv_comm_poly]

/-- The chain rule for a polynomial substitution. -/
theorem pderiv_bind₁_chain (F : Fin 3 → Poly) (j : Fin 3) (p : Poly) :
    pderiv j (bind₁ F p) = ∑ i, bind₁ F (pderiv i p) * pderiv j (F i) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]
  | mul_X p k ih =>
    have hsum : ∑ i, bind₁ F (pderiv i (X k : Poly)) * pderiv j (F i) = pderiv j (F k) := by
      simp [pderiv_X, Pi.single_apply]
    have e1 : ∑ i, bind₁ F p * bind₁ F (pderiv i (X k : Poly)) * pderiv j (F i) =
        bind₁ F p * pderiv j (F k) := by
      rw [← hsum, Finset.mul_sum]
      simp_rw [mul_assoc]
    have e2 : ∑ i, F k * bind₁ F (pderiv i p) * pderiv j (F i) =
        F k * ∑ i, bind₁ F (pderiv i p) * pderiv j (F i) := by
      rw [Finset.mul_sum]
      simp_rw [mul_assoc]
    rw [map_mul, bind₁_X_right, Derivation.leibniz, ih, smul_eq_mul, smul_eq_mul]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, bind₁_X_right, add_mul,
      Finset.sum_add_distrib, e1, e2]

end Calculus


section Parameter

/-- The `t`-derivative of `B(-t∂)` without the factor `∂_Z t`: `∑ b_r (-r) (-t)^(r-1) ∂ʳ`. -/
def bernoulliParam (n : ℕ) (t p : Poly) : Poly :=
  ∑ r ∈ Finset.range (n + 1), C ((bernoulli r : ℂ) / (r.factorial : ℂ)) *
    (C (-(r : ℂ)) * (-t) ^ (r - 1) * ((fun q : Poly => pderiv 0 q)^[r]) p)

/-- Product rule for the Bernoulli operator in the third variable `Z`. -/
theorem pderiv_two_bernoulliOperator (n : ℕ) (t p : Poly) :
    pderiv 2 (bernoulliOperator n t p) =
      bernoulliOperator n t (pderiv 2 p) + pderiv 2 t * bernoulliParam n t p := by
  unfold bernoulliOperator bernoulliParam
  rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_C_mul, pderiv_pow, map_neg,
    pderiv_iterate_comm]
  simp only [map_neg, map_natCast]
  ring

end Parameter


section Evaluation

variable {m : ℕ}

theorem pderiv_two_lit (i : Fin 3) : pderiv i (2 : Poly) = 0 := by
  rw [show (2 : Poly) = C 2 from (map_ofNat C 2).symm]; exact pderiv_C

theorem pderiv_two_bind (F : Fin 3 → Poly) (h0 : pderiv 2 (F 0) = 1) (h1 : pderiv 2 (F 1) = 0)
    (h2 : pderiv 2 (F 2) = 0) (q : Poly) : pderiv 2 (bind₁ F q) = bind₁ F (pderiv 0 q) := by
  rw [pderiv_bind₁_chain, Fin.sum_univ_three, h0, h1, h2]; simp

theorem bind_bernoulliParam (σ : Fin 3 → Poly)
    (hσ : ∀ i, pderiv 0 (σ i) = bind₁ σ (pderiv 0 (X i))) (n : ℕ) (t p : Poly) :
    bind₁ σ (bernoulliParam n t p) = bernoulliParam n (bind₁ σ t) (bind₁ σ p) := by
  have hd := TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers.pderiv_bind_commutes σ hσ
  unfold bernoulliParam
  simp only [map_sum, map_mul, map_pow, map_neg, bind₁_C_right]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers.derivative_iterate_bind_commutes σ hd]

/-- Even degree: simultaneous negation of the arguments fixes the polynomial. -/
theorem bind_neg_even_poly {d : ℕ} (w : Poly) (hw : w.IsHomogeneous d) (he : Even d) :
    bind₁ (fun i => -(X i : Poly)) w = w := by
  have h := TernaryPoly.homogeneous_bind_smul hw (-1 : ℂ)
  have ht : (fun i : Fin 3 => (-1 : ℂ) • (X i : Poly)) = fun i => -(X i : Poly) := by
    funext i; simp
  rw [ht, he.neg_one_pow, one_smul] at h
  exact h

theorem sigma_even {d : ℕ} (q : Poly) (hq : q.IsHomogeneous d) (he : Even d)
    (F K G : Fin 3 → Poly) (h1 : ∀ i, bind₁ sigma3 (F i) = G i)
    (h2 : ∀ i, bind₁ K (-(X i : Poly)) = G i) :
    bind₁ sigma3 (bind₁ F q) = bind₁ K q := by
  rw [bind_comp_coords sigma3 F G h1]
  have h := congrArg (bind₁ K) (bind_neg_even_poly q hq he)
  rw [bind₁_bind₁, funext h2] at h
  exact h

theorem tau_hFrame' (q : Poly) : bind₁ tauSub (bind₁ hFrame q) = bind₁ T1 q := by
  apply bind_comp_coords
  intro i
  fin_cases i
  · simp [tauSub, hFrame, T1]
  · simp [tauSub, hFrame, T1]
  · simp [tauSub, hFrame, T1]; ring

theorem tau_T1' (q : Poly) : bind₁ tauSub (bind₁ T1 q) = bind₁ T2 q := by
  apply bind_comp_coords
  intro i
  fin_cases i
  · simp [tauSub, T1, T2]
  · simp [tauSub, T1, T2]; ring
  · simp [tauSub, T1, T2, map_ofNat]; ring

/-- `(∂₁ψ₁)|_{Z=3Y} = v₁`: the first derivative frame. -/
theorem dpsi1_at_three (q : Poly) {d : ℕ} (hq : q.IsHomogeneous d) (he : Even d) :
    bind₁ sigma3 (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] q) = bind₁ hFrame q := by
  apply sigma_even q hq he _ _ ![X 1, -X 0, X 0 - X 1]
  · intro i
    fin_cases i
    · simp [sigma3_two, sigma3_one, map_ofNat]; ring
    · simp [sigma3_zero]
    · simp [sigma3_one, sigma3_zero]
  · intro i
    fin_cases i
    · simp [hFrame]
    · simp [hFrame]
    · simp [hFrame]

theorem dpsi2b_at_three (q : Poly) {d : ℕ} (hq : q.IsHomogeneous d) (he : Even d) :
    bind₁ sigma3 (bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] q) = bind₁ T1 q := by
  apply sigma_even q hq he _ _ ![X 1, X 1 - X 0, X 0 - 2 * X 1]
  · intro i
    fin_cases i
    · simp [sigma3_two, sigma3_one, map_ofNat]; ring
    · simp [sigma3_one, sigma3_zero]
    · simp [sigma3_one, sigma3_zero, map_ofNat]
  · intro i
    fin_cases i
    · simp [T1]
    · simp [T1]
    · simp [T1]

theorem bind_swap_pderiv (v : Poly)
    (hs : bind₁ (fun i => (X (Equiv.swap (0 : Fin 3) 2 i) : Poly)) v = v) (G : Fin 3 → Poly) :
    bind₁ G (pderiv 0 v) = bind₁ (fun i => G (Equiv.swap (0 : Fin 3) 2 i)) (pderiv 2 v) := by
  have s0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
  have s1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
  have s2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide
  have h := congrArg (pderiv (0 : Fin 3)) hs
  rw [pderiv_bind₁_chain, Fin.sum_univ_three] at h
  have x2 : pderiv (0 : Fin 3) (X 2 : Poly) = 0 := pderiv_X_of_ne (by decide)
  have x1 : pderiv (0 : Fin 3) (X 1 : Poly) = 0 := pderiv_X_of_ne (by decide)
  simp only [s0, s1, s2, x2, x1, pderiv_X_self, mul_zero, zero_add, mul_one, add_zero] at h
  rw [← h, bind₁_bind₁]
  simp only [bind₁_X_right]



theorem dpsi2a_at_three (v : HomogeneousPoly m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val) :
    bind₁ sigma3 (bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] (pderiv 0 v.val)) =
      bind₁ T2 (pderiv 2 v.val) := by
  have e1 : ∀ i, bind₁ sigma3 ((![X 2 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) i) =
      (![3 * X 1 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) i := by
    intro i
    fin_cases i
    · simp [sigma3_two, sigma3_zero]
    · simp [sigma3_one, sigma3_zero, map_ofNat]
    · simp [sigma3_one]
  rw [bind_comp_coords sigma3 _ _ e1, bind_swap_pderiv v.val (hs (Equiv.swap 0 2))]
  have s0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
  have s1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
  have s2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide
  have hf : (fun i => (![3 * X 1 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) (Equiv.swap (0 : Fin 3) 2 i)) = T2 := by
    funext i
    fin_cases i
    · simp [T2, s0]
    · simp [T2, s1]
    · simp [T2, s2]
  rw [hf]

/-- The `X`-derivative of `h`: `h_X = v₂ - v₃`. -/
theorem pderiv_zero_hFrame (q : Poly) :
    pderiv 0 (bind₁ hFrame q) = bind₁ hFrame (pderiv 1 q) - bind₁ hFrame (pderiv 2 q) := by
  rw [pderiv_bind₁_chain, Fin.sum_univ_three]
  have h0 : pderiv (0 : Fin 3) (hFrame 0) = 0 := by simp [hFrame]
  have h1 : pderiv (0 : Fin 3) (hFrame 1) = 1 := by simp [hFrame]
  have h2 : pderiv (0 : Fin 3) (hFrame 2) = -1 := by simp [hFrame]
  rw [h0, h1, h2]
  ring

theorem pderiv_two_form (n : ℕ) (ψ₁ ψ₂ : Poly) :
    pderiv 2 (X 2 * bernoulliOperator n (X 1) ψ₁ - X 1 * bernoulliOperator n (X 2) ψ₂) =
      bernoulliOperator n (X 1) ψ₁ + X 2 * bernoulliOperator n (X 1) (pderiv 2 ψ₁) -
        X 1 * (bernoulliOperator n (X 2) (pderiv 2 ψ₂) + bernoulliParam n (X 2) ψ₂) := by
  have a1 : pderiv (2 : Fin 3) (X 1 : Poly) = 0 := pderiv_X_of_ne (by decide)
  have a2 : pderiv (2 : Fin 3) (X 2 : Poly) = 1 := pderiv_X_self 2
  rw [map_sub, Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    pderiv_two_bernoulliOperator, pderiv_two_bernoulliOperator, a1, a2]
  ring


theorem pderiv_two_X0 : pderiv (2 : Fin 3) (X 0 : Poly) = 0 := pderiv_X_of_ne (by decide)
theorem pderiv_two_X1 : pderiv (2 : Fin 3) (X 1 : Poly) = 0 := pderiv_X_of_ne (by decide)
theorem pderiv_two_X2 : pderiv (2 : Fin 3) (X 2 : Poly) = 1 := pderiv_X_self 2
theorem pderiv_two_2X1 : pderiv (2 : Fin 3) (2 * X 1 : Poly) = 0 := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_two_lit, pderiv_two_X1]; ring

theorem pderiv_two_bind₃ (a b c : Poly) (ha : pderiv 2 a = 1) (hb : pderiv 2 b = 0)
    (hc : pderiv 2 c = 0) (q : Poly) :
    pderiv 2 (bind₁ ![a, b, c] q) = bind₁ ![a, b, c] (pderiv 0 q) :=
  pderiv_two_bind ![a, b, c] (by simpa using ha) (by simpa using hb) (by simpa using hc) q

theorem pderiv_two_a : pderiv 2 (X 2 - 2 * X 1 : Poly) = 1 := by
  rw [map_sub, pderiv_two_X2, pderiv_two_2X1]; ring
theorem pderiv_two_b : pderiv 2 (-X 0 : Poly) = 0 := by rw [map_neg, pderiv_two_X0]; ring
theorem pderiv_two_c : pderiv 2 (X 0 - X 1 : Poly) = 0 := by rw [map_sub, pderiv_two_X0, pderiv_two_X1]; ring
theorem pderiv_two_d : pderiv 2 (X 2 - X 0 : Poly) = 1 := by rw [map_sub, pderiv_two_X2, pderiv_two_X0]; ring
theorem pderiv_two_e : pderiv 2 (X 0 - 2 * X 1 : Poly) = 0 := by rw [map_sub, pderiv_two_X0, pderiv_two_2X1]; ring
theorem pderiv_two_f : pderiv 2 (-X 1 : Poly) = 0 := by rw [map_neg, pderiv_two_X1]; ring
theorem pderiv_two_g : pderiv 2 (X 1 - X 0 : Poly) = 0 := by rw [map_sub, pderiv_two_X0, pderiv_two_X1]; ring

theorem pderiv_two_psi1 (q : Poly) : pderiv (2 : Fin 3) (bind₁ (![X 2 - 2 * X 1, -X 0, X 0 - X 1] : Fin 3 → Poly) q) =
    bind₁ (![X 2 - 2 * X 1, -X 0, X 0 - X 1] : Fin 3 → Poly) (pderiv 0 q) :=
  pderiv_two_bind₃ _ _ _ pderiv_two_a pderiv_two_b pderiv_two_c q

theorem pderiv_two_psi2a (q : Poly) : pderiv (2 : Fin 3) (bind₁ (![X 2 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) q) =
    bind₁ (![X 2 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) (pderiv 0 q) :=
  pderiv_two_bind₃ _ _ _ pderiv_two_d pderiv_two_e pderiv_two_f q

theorem pderiv_two_psi2b (q : Poly) : pderiv (2 : Fin 3) (bind₁ (![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] : Fin 3 → Poly) q) =
    bind₁ (![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] : Fin 3 → Poly) (pderiv 0 q) :=
  pderiv_two_bind₃ _ _ _ pderiv_two_a pderiv_two_g pderiv_two_e q

/-- **The `Z`-derivative of `J_v` on `Z = 3Y`, before operator algebra.**  With
`h = v(-Y,X,Y-X)`, `v₁ = (∂₁v)(-Y,X,Y-X)`, `v₃ = (∂₃v)(-Y,X,Y-X)` and `τ` the translation `X ↦ X - Y`:
`∂_Z J_v|_{Z=3Y} = B(𝒟)(-h) + 3Y B(𝒟)v₁ - Y (B(3𝒟)(v₁ + τv₁ - τ²v₃) + B_Z'(3𝒟)(-(h + τh + τ²h)))`. -/
theorem bind_sigma3_pderiv_two_obstruction (v : HomogeneousPoly m) (hodd : Odd m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val) :
    bind₁ sigma3 (pderiv 2 (bernoulliObstruction v)) =
      bernoulliOperator m (X 1) (-bind₁ hFrame v.val) +
        3 * X 1 * bernoulliOperator m (X 1) (bind₁ hFrame (pderiv 0 v.val)) -
        X 1 * (bernoulliOperator m (3 * X 1)
            (bind₁ hFrame (pderiv 0 v.val) -
              bind₁ tauSub (bind₁ tauSub (bind₁ hFrame (pderiv 2 v.val))) +
              bind₁ tauSub (bind₁ hFrame (pderiv 0 v.val))) +
          bernoulliParam m (3 * X 1)
            (-(bind₁ hFrame v.val + bind₁ tauSub (bind₁ hFrame v.val) +
              bind₁ tauSub (bind₁ tauSub (bind₁ hFrame v.val))))) := by
  have hv : v.val.IsHomogeneous m := (mem_homogeneousSubmodule m v.val).mp v.2
  have hEven : Even (m - 1) := Nat.Odd.sub_odd hodd (by decide : Odd (1 : ℕ))
  have hq0 : (pderiv 0 v.val).IsHomogeneous (m - 1) :=
    TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers.pderiv_homogeneous v.val hv 0
  have hX1 : bind₁ sigma3 (X 1 : Poly) = X 1 := by rw [bind₁_X_right]; rfl
  have hX2 : bind₁ sigma3 (X 2 : Poly) = 3 * X 1 := by rw [bind₁_X_right]; rfl
  have hT1 : bind₁ T1 v.val = bind₁ tauSub (bind₁ hFrame v.val) := (tau_hFrame' _).symm
  have hT2 : bind₁ T2 v.val = bind₁ tauSub (bind₁ tauSub (bind₁ hFrame v.val)) := by
    rw [tau_hFrame', tau_T1']
  have hT1' : ∀ q : Poly, bind₁ T1 q = bind₁ tauSub (bind₁ hFrame q) := fun q => (tau_hFrame' q).symm
  have hT2' : ∀ q : Poly, bind₁ T2 q = bind₁ tauSub (bind₁ tauSub (bind₁ hFrame q)) := fun q => by
    rw [tau_hFrame', tau_T1']
  change bind₁ sigma3 (pderiv 2 (X 2 * bernoulliOperator m (X 1) (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] v.val) -
      X 1 * bernoulliOperator m (X 2) (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] v.val -
        bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] v.val +
        bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] v.val))) = _
  rw [pderiv_two_form]
  simp only [map_sub, map_add, map_mul, pderiv_two_psi1, pderiv_two_psi2a, pderiv_two_psi2b,
    bind_bernoulliOperator sigma3 sigma3_deriv, bind_bernoulliParam sigma3 sigma3_deriv, hX1, hX2,
    psi1_at_three v hodd, psi2_term2 v hs, psi2_term3 v hodd,
    dpsi1_at_three _ hq0 hEven, dpsi2a_at_three v hs, dpsi2b_at_three _ hq0 hEven, hT1', hT2']
  have harg : ∀ a b c : Poly, -a - c + -b = -(a + b + c) := by intros; ring
  rw [harg]

end Evaluation

end TernaryPeriodPolynomials.Argument.Identities.NormalJet
