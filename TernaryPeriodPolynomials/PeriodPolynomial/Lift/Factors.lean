module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodLift

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

private theorem binaryLiftEval_diagonal_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (a : TernaryPolynomial) : binaryLiftEval q a a = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  apply CharZero.eq_neg_self_iff.mp
  simpa only [coeff_neg] using congrArg (·.coeff d) (binaryLiftEval_swap hq a a)

private theorem binaryPeriodLift_diagonal_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (a b : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) a a b = 0 := by
  rw [binaryPeriodLift_substitute3, binaryLiftEval_diagonal_zero hq,
    binaryLiftEval_swap hq a b]
  ring

private theorem binaryPeriodLift_eval_cyclic (q : MvPolynomial (Fin 2) ℚ)
    (a b c : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) a b c = substitute3 (binaryPeriodLift q) b c a := by
  simp only [binaryPeriodLift_substitute3]
  abel

private theorem binaryPeriodLift_eval_neg_first {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (a b c : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) (-a) b c = substitute3 (binaryPeriodLift q) a b c := by
  simp only [binaryPeriodLift_substitute3, binaryLiftEval_neg_first hq,
    binaryLiftEval_neg_second hq]

private theorem binaryPeriodLift_eval_neg_second {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (a b c : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) a (-b) c = substitute3 (binaryPeriodLift q) a b c := by
  simp only [binaryPeriodLift_substitute3, binaryLiftEval_neg_first hq,
    binaryLiftEval_neg_second hq]

private theorem binaryPeriodLift_triangle_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (a b : TernaryPolynomial) :
    substitute3 (binaryPeriodLift q) (a+b) a b = 0 := by
  rw [binaryPeriodLift_substitute3, binaryLiftEval_swap hq (a+b) b]
  have h := binaryLiftEval_period hq (a+b) b
  simp only [add_sub_cancel_right] at h
  linear_combination -h

/-- Vanishing on the nine planes whose equations form the quotient's required factor. -/
structure BinaryLiftNinePlaneZeros (f : TernaryPolynomial) : Prop where
  eq01 : bind₁ (![X 1, X 1, X 2] : Fin 3 → TernaryPolynomial) f = 0
  neg01 : bind₁ (![-X 1, X 1, X 2] : Fin 3 → TernaryPolynomial) f = 0
  eq02 : bind₁ (![X 2, X 1, X 2] : Fin 3 → TernaryPolynomial) f = 0
  neg02 : bind₁ (![-X 2, X 1, X 2] : Fin 3 → TernaryPolynomial) f = 0
  eq12 : bind₁ (![X 0, X 2, X 2] : Fin 3 → TernaryPolynomial) f = 0
  neg12 : bind₁ (![X 0, -X 2, X 2] : Fin 3 → TernaryPolynomial) f = 0
  sum0 : bind₁ (![X 1+X 2, X 1, X 2] : Fin 3 → TernaryPolynomial) f = 0
  sum1 : bind₁ (![X 1-X 2, X 1, X 2] : Fin 3 → TernaryPolynomial) f = 0
  sum2 : bind₁ (![X 2-X 1, X 1, X 2] : Fin 3 → TernaryPolynomial) f = 0

/-- Binary alternation, evenness and the period equation kill all nine numerator planes. -/
theorem binaryPeriodLift_nine_planes_zero {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) : BinaryLiftNinePlaneZeros (binaryPeriodLift q) := by
  have h02 : substitute3 (binaryPeriodLift q) (X 2) (X 1) (X 2) = 0 := by
    rw [binaryPeriodLift_eval_cyclic q (X 2) (X 1) (X 2),
      binaryPeriodLift_eval_cyclic q (X 1) (X 2) (X 2), binaryPeriodLift_diagonal_zero hq]
  have h12 : substitute3 (binaryPeriodLift q) (X 0) (X 2) (X 2) = 0 := by
    rw [binaryPeriodLift_eval_cyclic q, binaryPeriodLift_diagonal_zero hq]
  refine ⟨binaryPeriodLift_diagonal_zero hq (X 1) (X 2), ?_, h02, ?_, h12, ?_,
    binaryPeriodLift_triangle_zero hq (X 1) (X 2), ?_, ?_⟩
  · change substitute3 (binaryPeriodLift q) (-X 1) (X 1) (X 2) = 0
    rw [binaryPeriodLift_eval_neg_first hq, binaryPeriodLift_diagonal_zero hq]
  · change substitute3 (binaryPeriodLift q) (-X 2) (X 1) (X 2) = 0
    rw [binaryPeriodLift_eval_neg_first hq, h02]
  · change substitute3 (binaryPeriodLift q) (X 0) (-X 2) (X 2) = 0
    rw [binaryPeriodLift_eval_neg_second hq, h12]
  · change substitute3 (binaryPeriodLift q) (X 1-X 2) (X 1) (X 2) = 0
    rw [binaryPeriodLift_eval_cyclic q]
    have h := binaryPeriodLift_triangle_zero hq (X 2) (X 1-X 2)
    rwa [show (X 2+(X 1-X 2) : TernaryPolynomial) = X 1 by ring] at h
  · change substitute3 (binaryPeriodLift q) (X 2-X 1) (X 1) (X 2) = 0
    rw [binaryPeriodLift_eval_cyclic q (X 2-X 1) (X 1) (X 2),
      binaryPeriodLift_eval_cyclic q (X 1) (X 2) (X 2-X 1)]
    have h := binaryPeriodLift_triangle_zero hq (X 2-X 1) (X 1)
    simpa only [sub_add_cancel] using h


private theorem quotient_specialization_zero (f l : TernaryPolynomial)
    (v : Fin 3 → TernaryPolynomial) (hl : f = (X 0+X 1+X 2)*l)
    (hz : bind₁ v f = 0) (hW : bind₁ v (X 0+X 1+X 2) ≠ 0) : bind₁ v l = 0 := by
  rw [hl, map_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hW

/-- These nine planes survive division by the coordinate sum. -/
theorem BinaryLiftNinePlaneZeros.of_coordinate_sum_mul {f l : TernaryPolynomial}
    (hf : BinaryLiftNinePlaneZeros f) (hl : f = (X 0+X 1+X 2)*l) :
    BinaryLiftNinePlaneZeros l := by
  constructor
  · apply quotient_specialization_zero f l _ hl hf.eq01
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.neg01
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.eq02
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.neg02
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.eq12
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.neg12
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.sum0
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.sum1
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he
  · apply quotient_specialization_zero f l _ hl hf.sum2
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [Matrix.cons_val_two] at he

private theorem update_X_zero (p : TernaryPolynomial) :
    Function.update X (0 : Fin 3) p = ![p, X 1, X 2] := by
  funext i
  fin_cases i <;> simp

private theorem update_X_one (p : TernaryPolynomial) :
    Function.update X (1 : Fin 3) p = ![X 0, p, X 2] := by
  funext i
  fin_cases i <;> simp

/-- The nine distinct zero planes supply their full product as a divisor. -/
theorem binaryLiftNineFactor_dvd_of_planes_zero {f : TernaryPolynomial}
    (hf : BinaryLiftNinePlaneZeros f) :
    (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2) * (X 0+X 1-X 2) ∣ f := by
  have h1 : (X 0-X 1) ∣ f :=
    linear_factor_dvd_of_substitution_zero f 0 (X 1)
      (by simpa only [update_X_zero] using hf.eq01)
  have hk2 : bind₁ (Function.update X (0 : Fin 3) (-X 1))
      ((X 0-X 1) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at he
  have h2 : (X 0-X 1) * (X 0+X 1) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1)) 0 (-X 1) h1
      (by simpa only [update_X_zero] using hf.neg01) hk2
    simpa only [sub_neg_eq_add] using h
  have hk3 : bind₁ (Function.update X (0 : Fin 3) (X 2))
      ((X 0-X 1) * (X 0+X 1) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at he
  have h3 : (X 0-X 1) * (X 0+X 1) * (X 0-X 2) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1) * (X 0+X 1)) 0 (X 2) h2
      (by simpa only [update_X_zero] using hf.eq02) hk3
    exact h
  have hk4 : bind₁ (Function.update X (0 : Fin 3) (-X 2))
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at he
  have h4 : (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2)) 0 (-X 2) h3
      (by simpa only [update_X_zero] using hf.neg02) hk4
    simpa only [sub_neg_eq_add] using h
  have hk5 : bind₁ (Function.update X (1 : Fin 3) (X 2))
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_one, Matrix.cons_val_two] at he
  have h5 : (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2)) 1 (X 2) h4
      (by simpa only [update_X_one] using hf.eq12) hk5
    exact h
  have hk6 : bind₁ (Function.update X (1 : Fin 3) (-X 2))
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_one, Matrix.cons_val_two] at he
  have h6 : (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2)) 1 (-X 2) h5
      (by simpa only [update_X_one] using hf.neg12) hk6
    simpa only [sub_neg_eq_add] using h
  have hk7 : bind₁ (Function.update X (0 : Fin 3) (X 1+X 2))
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at he
  have h7 : (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2)) 0 (X 1+X 2) h6
      (by simpa only [update_X_zero] using hf.sum0) hk7
    rw [show (X 0-(X 1+X 2) : TernaryPolynomial) = X 0-X 1-X 2 by ring] at h
    exact h
  have hk8 : bind₁ (Function.update X (0 : Fin 3) (X 1-X 2))
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at he
  have h8 : (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2)) 0 (X 1-X 2) h7
      (by simpa only [update_X_zero] using hf.sum1) hk8
    rw [show (X 0-(X 1-X 2) : TernaryPolynomial) = X 0-X 1+X 2 by ring] at h
    exact h
  have hk9 : bind₁ (Function.update X (0 : Fin 3) (X 2-X 1))
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at he
  have h9 : (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2) * (X 0+X 1-X 2) ∣ f := by
    have h := mul_linear_factor_dvd_of_substitution_zero f
      ((X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2)) 0 (X 2-X 1) h8
      (by simpa only [update_X_zero] using hf.sum2) hk9
    rw [show (X 0-(X 2-X 1) : TernaryPolynomial) = X 0+X 1-X 2 by ring] at h
    exact h
  exact h9

/-- The quotient of a binary period lift by the coordinate sum contains all nine factors. -/
theorem binaryLiftNineFactor_dvd_quotient {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) (l : TernaryPolynomial)
    (hl : binaryPeriodLift q = (X 0+X 1+X 2)*l) :
    (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) * (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2) * (X 0+X 1-X 2) ∣ l :=
  binaryLiftNineFactor_dvd_of_planes_zero
    ((binaryPeriodLift_nine_planes_zero hq).of_coordinate_sum_mul hl)

end TernaryPoly
