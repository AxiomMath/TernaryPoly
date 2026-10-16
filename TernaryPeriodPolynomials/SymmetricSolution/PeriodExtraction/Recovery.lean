module

public import TernaryPeriodPolynomials.SymmetricSolution.PeriodExtraction.Basic

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly
local notation "BP" => MvPolynomial (Fin 2) ℚ
open SymmetricPeriodExtraction

/-- Separate oddness gives the normalization axis for every symmetric binary period. -/
theorem symmetricBinaryPeriod_axis_first {q : BP} (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ (![0,X 1] : Fin 2 → BP) q=0 := by
  have h := congrArg (bs 0 (X 1)) hq.odd_first
  change bs 0 (X 1) (bs (-X 0) (X 1) q)=_ at h
  rw [bs_comp] at h
  have ht : bs 0 (X 1) q= -bs 0 (X 1) q := by simpa [bs] using h
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp ht)

private theorem mixed_pderiv_commute (q : BP) :
    pderiv 1 (pderiv 0 q)=pderiv 0 (pderiv 1 q) := by
  classical
  ext d
  simp only [coeff_pderiv]
  simp [Finsupp.add_apply,add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm]

/-- The two derivative signs cancel the odd quarter-rotation sign of the period. -/
theorem symmetricBinaryPeriod_mixed_boundary_rotation {q : BP}
    (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ ![-X 1,X 0] (pderiv 0 (pderiv 1 q))=pderiv 0 (pderiv 1 q) := by
  have hrot : (bind₁ ![-X 1,X 0] q : BP)= -q := by
    have h := congrArg (bind₁ (![X 1,X 0] : Fin 2 → BP)) hq.odd_first
    rw [bind_comp] at h
    simp only [map_neg,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one] at h
    rw [hq.swap] at h
    exact h
  have h := congrArg (fun r : BP => pderiv 0 (pderiv 1 r)) hrot
  simpa [binary_pderiv_substitution,mixed_pderiv_commute] using h

private theorem boundary_lift_eval (q : BP) :
    binaryBoundary (binaryLiftEval q (X 0) (X 1))=bind₁ ![-X 1,X 0] q := by
  simp only [binaryBoundary,binaryLiftEval,bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The boundary partial sum of a symmetric period quotient is its binary mixed derivative. -/
theorem symmetricBinaryLift_boundary_partial_sum {q : BP} (hq : SymmetricBinaryPeriodRelations q)
    (f : TernaryPolynomial) (hl : binaryPeriodLift q=(X 0+X 1+X 2)*f) :
    binaryBoundary (pderiv 0 f+pderiv 1 f)=pderiv 0 (pderiv 1 q) := by
  have h := congrArg (fun r : TernaryPolynomial => binaryBoundary (pderiv 0 (pderiv 1 r))) hl
  rw [binaryPeriodLift_mixed_derivative,boundary_lift_eval,
    symmetricBinaryPeriod_mixed_boundary_rotation hq,binaryBoundary_mixed_coordinate_sum_mul] at h
  exact h.symm

/-- Normalized first-jet extraction recovers the second partial of a symmetric period. -/
theorem symmetricBinaryFirstJetPrimitive_lift_quotient {q : BP}
    (hq : SymmetricBinaryPeriodRelations q) (f : TernaryPolynomial)
    (hl : binaryPeriodLift q=(X 0+X 1+X 2)*f) :
    binaryFirstJetPrimitive f= -pderiv 1 q := by
  have haxis : bind₁ (![0,X 1] : Fin 2 → BP) (pderiv 1 q)=0 := by
    have h := congrArg (pderiv (1 : Fin 2)) (symmetricBinaryPeriod_axis_first hq)
    simpa [binary_pderiv_substitution] using h
  rw [binaryFirstJetPrimitive,symmetricBinaryLift_boundary_partial_sum hq f hl,
    binaryIntegral_pderiv_of_axis _ haxis]

/-- Euler's formula recovers the entire homogeneous symmetric binary period from a lift quotient. -/
theorem symmetricBinaryPeriodPrimitive_recovery {q : BP} {n : ℕ}
    (hq : SymmetricBinaryPeriodRelations q) (hdeg : q.IsHomogeneous (n+1))
    (f : TernaryPolynomial) (hl : binaryPeriodLift q=(X 0+X 1+X 2)*f) :
    binaryPeriodPrimitive n (binaryFirstJetPrimitive f)=q := by
  have hrot : binaryRotation q= -q := by
    have h := congrArg (bind₁ (![-X 0,X 1] : Fin 2 → BP)) hq.swap
    rw [bind_comp,hq.odd_first] at h
    simpa [binaryRotation] using h
  have hder : binaryRotation (pderiv 1 q)=pderiv 0 q := by
    have h := congrArg (pderiv (0 : Fin 2)) hrot
    simpa [binaryRotation,binary_pderiv_substitution] using h
  have he : X 0*pderiv 0 q+X 1*pderiv 1 q=((n : ℚ)+1) • q := by
    rw [show (n : ℚ)+1=((n+1 : ℕ) : ℚ) by simp, Nat.cast_smul_eq_nsmul]
    simpa only [Fin.sum_univ_two] using hdeg.sum_X_mul_pderiv
  rw [symmetricBinaryFirstJetPrimitive_lift_quotient hq f hl,binaryPeriodPrimitive]
  have hn : binaryRotation (-pderiv 1 q)= -pderiv 0 q := by
    simpa only [binaryRotation,map_neg] using congrArg Neg.neg hder
  rw [hn,mul_neg,mul_neg,← neg_add,smul_neg,neg_smul,neg_neg,he,smul_smul,
    div_mul_cancel₀ 1 (Nat.cast_add_one_ne_zero n),one_smul]

end TernaryPoly
