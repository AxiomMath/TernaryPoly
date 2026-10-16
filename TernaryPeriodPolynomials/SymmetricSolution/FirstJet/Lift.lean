module

public import TernaryPeriodPolynomials.SymmetricSolution.FirstJet.LiftDifference
public import TernaryPeriodPolynomials.Polynomial.TernaryThirdVariable
public import TernaryPeriodPolynomials.Polynomial.TripleDifference

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricFirstLift

/-- The first-two-coordinate norm preserves oddness in the third coordinate. -/
theorem norm_odd {Q : TernaryPolynomial}
    (ho : bind₁ ![X 0,X 1,-X 2] Q= -Q) :
    bind₁ ![X 0,X 1,-X 2] (N Q)= -N Q := by
  change substitute3 (N Q) (X 0) (X 1) (-X 2)= -N Q
  rw [substitute3_norm]
  simp only [SymmetricFirstLiftEvaluation.odd_eval ho]
  have hv : (![X 0,X 1,X 2] : Fin 3 → TernaryPolynomial)=X := by
    funext i
    fin_cases i <;> rfl
  simp only [substitute3,N_apply,A,A2,hv,bind₁_X_left,AlgHom.id_apply]
  abel

private theorem first_step_ne_zero : (X 0 : TernaryThirdVariable.Binary)≠0 := by
  exact X_ne_zero 0

private theorem second_step_ne_zero : (-X 1 : TernaryThirdVariable.Binary)≠0 := by
  exact neg_ne_zero.mpr (X_ne_zero 1)

private theorem third_step_ne_zero : (X 1-X 0 : TernaryThirdVariable.Binary)≠0 := by
  intro h
  have he := congrArg (eval (![0,1] : Fin 2 → ℚ)) h
  norm_num at he

/-- A symmetric odd first mixed lift has zero norm, with no degree bound. -/
theorem norm_zero {f Q : TernaryPolynomial}
    (hc : C f=f) (hs : S f=f) (hf : N f=0) (hqs : S Q=Q)
    (ho : bind₁ ![X 0,X 1,-X 2] Q= -Q)
    (hm : bind₁ ![X 0,X 1,X 2+X 0] Q-Q=bind₁ ![X 0+X 2,-X 2,X 1] f) :
    N Q=0 := by
  have ht := SymmetricFirstLiftDifference.norm_triple_difference hc hs hf hm (X 0) (X 1) (X 2)
  have hdifference := TernaryThirdVariable.toPoly_triple_difference ht
  have hd := PolynomialTripleDifference.third_derivative_eq_zero
    first_step_ne_zero second_step_ne_zero third_step_ne_zero hdifference
  have hodd := TernaryThirdVariable.toPoly_odd (norm_odd ho)
  have heval := TernaryThirdVariable.toPoly_eval_zero
    (SymmetricFirstLiftEvaluation.norm_at_step hc hs hf hqs ho hm (X 0) (X 1))
  have hz := PolynomialTripleDifference.eq_zero_of_third_derivative_odd_eval
    (TernaryThirdVariable.toPoly (N Q)) first_step_ne_zero hd hodd heval
  apply TernaryThirdVariable.toPoly_injective
  simpa only [map_zero] using hz

end TernaryPoly.SymmetricFirstLift
