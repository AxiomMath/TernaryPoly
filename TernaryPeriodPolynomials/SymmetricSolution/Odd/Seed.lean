module

public import TernaryPeriodPolynomials.SymmetricSolution.PeriodSeeds
public import TernaryPeriodPolynomials.Polynomial.Divisibility

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly

private theorem first_pair_sum_ne_zero : (X 0+X 1 : TernaryPolynomial)≠0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ℚ)) h
  norm_num at he

/-- The apparent support-two pole of the lowest odd layer always cancels. -/
theorem symmetricOddSeedQ_dvd {q : MvPolynomial (Fin 2) ℚ}
    (hq : SymmetricBinaryPeriodRelations q) :
    (X 0+X 1 : TernaryPolynomial) ∣ symmetricPeriodSeedQ 0 q := by
  have hv : Function.update (X : Fin 3 → TernaryPolynomial) 1 (-X 0)=![X 0,-X 0,X 2] := by
    funext i
    fin_cases i <;> simp
  have hz : bind₁ (Function.update X 1 (-X 0)) (symmetricPeriodSeedQ 0 q)=0 := by
    rw [hv]
    change substitute3 (symmetricPeriodSeedQ 0 q) (X 0) (-X 0) (X 2)=0
    rw [symmetricPeriodSeedQ_substitute,symmetricBinaryEval_neg_first hq]
    simp
  have h := linear_factor_dvd_of_substitution_zero (symmetricPeriodSeedQ 0 q) 1 (-X 0) hz
  simpa only [sub_neg_eq_add,add_comm] using h

/-- The actual polynomial support-two seed of the lowest odd tower layer. -/
def symmetricOddSeedQ (q : MvPolynomial (Fin 2) ℚ) (hq : SymmetricBinaryPeriodRelations q) :
    TernaryPolynomial := Classical.choose (symmetricOddSeedQ_dvd hq)

theorem symmetricOddSeedQ_mul (q : MvPolynomial (Fin 2) ℚ) (hq : SymmetricBinaryPeriodRelations q) :
    (X 0+X 1)*symmetricOddSeedQ q hq=symmetricPeriodSeedQ 0 q :=
  (Classical.choose_spec (symmetricOddSeedQ_dvd hq)).symm

/-- Polynomial cancellation retains the literal swap symmetry. -/
theorem symmetricOddSeedQ_swap (q : MvPolynomial (Fin 2) ℚ) (hq : SymmetricBinaryPeriodRelations q) :
    S (symmetricOddSeedQ q hq)=symmetricOddSeedQ q hq := by
  apply mul_left_cancel₀ first_pair_sum_ne_zero
  have h := congrArg S (symmetricOddSeedQ_mul q hq)
  rw [map_mul,symmetricPeriodSeedQ_swap] at h
  have hw : S (X 0+X 1)= (X 0+X 1 : TernaryPolynomial) := by simp [S,add_comm]
  rw [hw,←symmetricOddSeedQ_mul q hq] at h
  exact h

/-- Polynomial cancellation retains oddness in the third coordinate. -/
theorem symmetricOddSeedQ_odd (q : MvPolynomial (Fin 2) ℚ) (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ ![X 0,X 1,-X 2] (symmetricOddSeedQ q hq)= -symmetricOddSeedQ q hq := by
  apply mul_left_cancel₀ first_pair_sum_ne_zero
  have h := congrArg (fun p : TernaryPolynomial => bind₁ (![X 0,X 1,-X 2] : Fin 3 → TernaryPolynomial) p) (symmetricOddSeedQ_mul q hq)
  rw [map_mul,symmetricPeriodSeedQ_odd 0 hq] at h
  have hw : bind₁ (![X 0,X 1,-X 2] : Fin 3 → TernaryPolynomial) (X 0+X 1 : TernaryPolynomial)=X 0+X 1 := by simp
  rw [hw,←symmetricOddSeedQ_mul q hq] at h
  simpa only [mul_neg] using h

/-- The cancelled support-two seed satisfies the literal mixed equation for every quotient by W. -/
theorem symmetricOddSeedQ_mixed (q : MvPolynomial (Fin 2) ℚ) (hq : SymmetricBinaryPeriodRelations q)
    (f : TernaryPolynomial) (hf : binaryPeriodLift q=(X 0+X 1+X 2)*f) :
    bind₁ ![X 0,X 1,X 2+X 0] (symmetricOddSeedQ q hq)-symmetricOddSeedQ q hq=
      bind₁ ![X 0+X 2,-X 2,X 1] f := by
  apply mul_left_cancel₀ first_pair_sum_ne_zero
  have h := symmetricPeriodSeedQ_mixed 0 hq (X 0) (X 1) (X 2)
  simp only [pow_zero,one_mul] at h
  have hQ := congrArg (fun p : TernaryPolynomial => bind₁ (![X 0,X 1,X 2+X 0] : Fin 3 → TernaryPolynomial) p) (symmetricOddSeedQ_mul q hq)
  have hf' := congrArg (fun p : TernaryPolynomial => bind₁ (![X 0+X 2,-X 2,X 1] : Fin 3 → TernaryPolynomial) p) hf
  have hwQ : bind₁ (![X 0,X 1,X 2+X 0] : Fin 3 → TernaryPolynomial) (X 0+X 1 : TernaryPolynomial)=X 0+X 1 := by simp
  have hwf : bind₁ (![X 0+X 2,-X 2,X 1] : Fin 3 → TernaryPolynomial) (X 0+X 1+X 2 : TernaryPolynomial)=X 0+X 1 := by
    simp
  rw [map_mul,hwQ] at hQ
  rw [map_mul,hwf] at hf'
  have hself (p : TernaryPolynomial) : substitute3 p (X 0) (X 1) (X 2)=p := by
    have hv : (![X 0,X 1,X 2] : Fin 3 → TernaryPolynomial)=X := by
      funext i
      fin_cases i <;> rfl
    simp only [substitute3,hv,bind₁_X_left,AlgHom.id_apply]
  rw [hself] at h
  change bind₁ ![X 0,X 1,X 2+X 0] (symmetricPeriodSeedQ 0 q)-symmetricPeriodSeedQ 0 q=
    bind₁ ![X 0+X 2,-X 2,X 1] (binaryPeriodLift q) at h
  rw [mul_sub,hQ,symmetricOddSeedQ_mul,hf'.symm]
  exact h

end TernaryPoly
