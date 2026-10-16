module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodLift
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Basic

@[expose] public section


open MvPolynomial

noncomputable section
namespace TernaryPoly

local notation "BP" => MvPolynomial (Fin 2) ℚ

private theorem binary_bind_chain_rule {σ : Type*} (q : BP)
    (a b : MvPolynomial σ ℚ) (i : σ) :
    pderiv i (bind₁ ![a,b] q) = bind₁ ![a,b] (pderiv 0 q) * pderiv i a +
      bind₁ ![a,b] (pderiv 1 q) * pderiv i b := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp => fin_cases j <;> simp [map_mul, map_add, hp] <;> ring

private theorem binary_bind_comp (p a b c d : BP) :
    bind₁ ![a,b] (bind₁ ![c,d] p) =
      bind₁ ![bind₁ ![a,b] c, bind₁ ![a,b] d] p := by
  rw [bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem binary_mixed_pderiv_commute (q : BP) :
    pderiv 1 (pderiv 0 q) = pderiv 0 (pderiv 1 q) := by
  classical
  ext d
  simp only [coeff_pderiv]
  simp [Finsupp.add_apply, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm]

/-- The mixed derivative of an even alternating binary polynomial is invariant under the boundary rotation. -/
theorem binaryPeriod_mixed_boundary_rotation {q : BP} (hq : BinaryPeriodRelations q) :
    bind₁ ![-X 1, X 0] (pderiv 0 (pderiv 1 q)) = pderiv 0 (pderiv 1 q) := by
  have hrot : bind₁ ![-X 1, X 0] q = -q := by
    have h := congrArg (bind₁ (![X 1, X 0] : Fin 2 → BP)) hq.even_first
    rw [binary_bind_comp] at h
    simp only [map_neg, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact h.trans hq.swap
  have h := congrArg (fun r : BP => pderiv 0 (pderiv 1 r)) hrot
  simpa [binary_bind_chain_rule, binary_mixed_pderiv_commute] using h

/-- Only the first summand in the cyclic lift contributes to its first mixed derivative. -/
theorem binaryPeriodLift_mixed_derivative (q : BP) :
    pderiv 0 (pderiv 1 (binaryPeriodLift q)) =
      binaryLiftEval (pderiv 0 (pderiv 1 q)) (X 0) (X 1) := by
  simp [binaryPeriodLift, binaryLiftEval, binary_bind_chain_rule]

private theorem binaryBoundary_binaryLiftEval (q : BP) :
    binaryBoundary (binaryLiftEval q (X 0) (X 1)) = bind₁ ![-X 1, X 0] q := by
  simp only [binaryBoundary, binaryLiftEval, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

/-- Restricting a mixed derivative of `W*l` to `W=0` leaves the sum of the first two partials of `l`. -/
theorem binaryBoundary_mixed_coordinate_sum_mul (l : TernaryPolynomial) :
    binaryBoundary (pderiv 0 (pderiv 1 ((X 0+X 1+X 2)*l))) =
      binaryBoundary (pderiv 0 l+pderiv 1 l) := by
  have hd : pderiv 0 (pderiv 1 ((X 0+X 1+X 2)*l)) =
      pderiv 0 l + pderiv 1 l + (X 0+X 1+X 2)*pderiv 0 (pderiv 1 l) := by
    simp
    ring
  rw [hd]
  simp [binaryBoundary]

/-- The quotient lift recovers the mixed derivative of the original binary polynomial on the boundary. -/
theorem binaryLift_boundary_partial_sum {q : BP} (hq : BinaryPeriodRelations q)
    (l : TernaryPolynomial) (hl : binaryPeriodLift q = (X 0+X 1+X 2)*l) :
    binaryBoundary (pderiv 0 l+pderiv 1 l) = pderiv 0 (pderiv 1 q) := by
  have h := congrArg (fun r : TernaryPolynomial => binaryBoundary (pderiv 0 (pderiv 1 r))) hl
  rw [binaryPeriodLift_mixed_derivative, binaryBoundary_binaryLiftEval,
    binaryPeriod_mixed_boundary_rotation hq, binaryBoundary_mixed_coordinate_sum_mul] at h
  exact h.symm

/-- Normalized binary integration recovers a polynomial whose integration axis is zero. -/
theorem binaryIntegral_pderiv_of_axis (q : BP)
    (hq : bind₁ (![0, X 1] : Fin 2 → BP) q = 0) :
    binaryIntegral (pderiv 0 q) = q := by
  have haxis := congrArg (finSuccEquiv ℚ 1) hq
  rw [finSuccEquiv_bind_zero, map_zero] at haxis
  have heval : Polynomial.eval 0 (finSuccEquiv ℚ 1 q) = 0 :=
    Polynomial.C_injective (by simpa only [map_zero] using haxis)
  have hconst : (finSuccEquiv ℚ 1 q).coeff 0 = 0 := by
    rwa [Polynomial.coeff_zero_eq_eval_zero]
  apply (finSuccEquiv ℚ 1).injective
  rw [finSuccEquiv_binaryIntegral, finSuccEquiv_pderiv_zero_general]
  exact (polyIntegral_unique _ _ rfl hconst).symm

/-- The normalized first-jet primitive of a cyclic period lift quotient is minus its second binary partial. -/
theorem binaryFirstJetPrimitive_binaryPeriodLift_quotient {q : BP}
    (hq : BinaryPeriodRelations q) (l : TernaryPolynomial)
    (hl : binaryPeriodLift q = (X 0+X 1+X 2)*l) :
    binaryFirstJetPrimitive l = -pderiv 1 q := by
  have haxis : bind₁ (![0, X 1] : Fin 2 → BP) (pderiv 1 q) = 0 := by
    have h := congrArg (pderiv (1 : Fin 2)) hq.axis_first
    simpa [binary_bind_chain_rule] using h
  rw [binaryFirstJetPrimitive, binaryLift_boundary_partial_sum hq l hl,
    binaryIntegral_pderiv_of_axis _ haxis]

end TernaryPoly
