module

public import TernaryPeriodPolynomials.SymmetricSolution.HSymmetry.J

@[expose] public section


/-!
# `p_parity` for the paper's own `p = -∫₀^X H(s,Y) ds`, with no hypotheses on `p`

Formalized by Claude Haiku 5.5.

The paper's `p` is `NormalJet.periodP` (three variables over ℂ, `antiderivX` of `periodH`).
Its binary form is `q = -antiQ (HJet v)`, where `antiQ` is the `X₀`-antiderivative over ℚ of a
binary polynomial. We show `periodP (cpx v) = liftJ q` by the uniqueness lemma
`eq_of_pderiv0_of_bind`, and then `hp₁ : ∂_X q = -HJet v` and `hp₀ : q(0,Y) = 0` are direct.
So `p_parity` applies to `q` with `hm`, `v`, `hv`, `S`, `C`, `J_v = 0` as the only hypotheses.
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.HSymmetryPeriodP

open TernaryPeriodPolynomials.Argument.Identities
open TernaryPeriodPolynomials.Argument.Identities.HSymmetryJ

/-- The `X₀`-antiderivative of a binary ℚ-polynomial, `X₀^a X₁^b ↦ X₀^(a+1) X₁^b / (a+1)`. -/
def antiQ (c : MvPolynomial (Fin 2) ℚ) : MvPolynomial (Fin 2) ℚ :=
  ∑ s ∈ c.support, monomial (s + Finsupp.single (0 : Fin 2) 1) (c.coeff s / ((s 0 : ℚ) + 1))

theorem pderiv0_antiQ (c : MvPolynomial (Fin 2) ℚ) : pderiv 0 (antiQ c) = c := by
  conv_rhs => rw [c.as_sum]
  unfold antiQ
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pderiv_monomial]
  simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  congr 1
  push_cast
  have : ((s 0 : ℚ) + 1) ≠ 0 := by positivity
  field_simp

theorem bind_zero_antiQ (c : MvPolynomial (Fin 2) ℚ) :
    bind₁ (![0, X 1] : HSymmetry.HSub2) (antiQ c) = 0 := by
  unfold antiQ
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hz : ∏ i ∈ (s + Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ).support,
      (![0, X 1] : HSymmetry.HSub2) i ^ (s + Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) i = 0 :=
    Finset.prod_eq_zero (i := 0) (by simp) (by simp)
  rw [bind₁_monomial, hz, mul_zero]

/-- `X₀ ↦ 0` commutes with the lift `liftJ` of binary polynomials. -/
theorem s0C_bind_liftJ_eq (p : MvPolynomial (Fin 2) ℚ) :
    bind₁ s0C (liftJ p) = liftJ (bind₁ (![0, X 1] : HSymmetry.HSub2) p) := by
  have h := liftJ_bind (![0, X 1] : HSymmetry.HSub2) p
  rw [h]
  have hs0 : (s0C ∘ Fin.castSucc) =
      fun j => rename Fin.castSucc (cpx ((![0, X 1] : HSymmetry.HSub2) j)) := by
    funext j
    fin_cases j <;> simp [s0C, cpx]
  unfold liftJ
  rw [bind₁_rename, hs0]

/-- **The paper's `p` is a lift of a binary polynomial:** `periodP (cpx v) = liftJ (-antiQ (HJet v))`. -/
theorem periodP_eq_liftJ_anti (v : MvPolynomial (Fin 3) ℚ) :
    NormalJet.periodP (cpx v) = liftJ (-antiQ (HSymmetry.HJet v)) := by
  apply eq_of_pderiv0_of_bind
  · rw [pderiv0_periodP, pderiv0_liftJ, map_neg, pderiv0_antiQ, liftJ_neg]
  · rw [bind_s0_periodP, s0C_bind_liftJ_eq, map_neg, bind_zero_antiQ, neg_zero, liftJ_zero]

/-- **`p_parity` for the paper's `p`**. For a homogeneous odd symmetric `v` over `ℚ` with
`J_v = 0`, the binary polynomial `p = -∫₀^X H(s,Y) ds` (its lift is the paper's `periodP`) satisfies
the five clauses of `eq:H-symmetry` and `lem:period-extraction`. No hypothesis on `p` is needed. -/
theorem p_parity_periodP {m : ℕ} (hm : Odd m) (v : MvPolynomial (Fin 3) ℚ)
    (hv : v.IsHomogeneous m)
    (hS : bind₁ (![X 1, X 0, X 2] : HSymmetry.HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSymmetry.HSub3) v = v)
    (hJ : bernoulliObstruction (complexify v hv) = 0) :
    liftJ (-antiQ (HSymmetry.HJet v)) = NormalJet.periodP (cpx v) ∧
    bind₁ (![-X 0, X 1] : HSymmetry.HSub2) (HSymmetry.HJet v) = HSymmetry.HJet v ∧
      bind₁ (![X 0, -X 1] : HSymmetry.HSub2) (HSymmetry.HJet v) = HSymmetry.HJet v ∧
      bind₁ (![-X 0, X 1] : HSymmetry.HSub2) (-antiQ (HSymmetry.HJet v)) = -(-antiQ (HSymmetry.HJet v)) ∧
      bind₁ (![X 0, -X 1] : HSymmetry.HSub2) (-antiQ (HSymmetry.HJet v)) = -antiQ (HSymmetry.HJet v) ∧
      pderiv 0 (-antiQ (HSymmetry.HJet v)) =
        bind₁ (![X 1, -X 0] : HSymmetry.HSub2) (pderiv 0 (-antiQ (HSymmetry.HJet v))) := by
  have hp₁ : pderiv 0 (-antiQ (HSymmetry.HJet v)) = -HSymmetry.HJet v := by
    rw [map_neg, pderiv0_antiQ]
  have hp₀ : bind₁ (![0, X 1] : HSymmetry.HSub2) (-antiQ (HSymmetry.HJet v)) = 0 := by
    rw [map_neg, bind_zero_antiQ, neg_zero]
  obtain ⟨c1, c2, c3, c4, c5⟩ := p_parity_of_J_zero hm v hv hS hC _ hp₁ hp₀ hJ
  exact ⟨(periodP_eq_liftJ_anti v).symm, c1, c2, c3, c4, c5⟩

end TernaryPeriodPolynomials.Argument.Identities.HSymmetryPeriodP
