module

public import TernaryPeriodPolynomials.SymmetricSolution.Boundary
public import TernaryPeriodPolynomials.Polynomial.Divisibility

@[expose] public section


open MvPolynomial

namespace TernaryPoly

open SymmetricCertificate

private theorem update_X_zero (p : TernaryPolynomial) :
    Function.update X (0 : Fin 3) p = ![p, X 1, X 2] := by
  funext i
  fin_cases i <;> simp

private theorem update_X_one (p : TernaryPolynomial) :
    Function.update X (1 : Fin 3) p = ![X 0, p, X 2] := by
  funext i
  fin_cases i <;> simp

/-- The three opposite-coordinate planes supply their full product as a factor. -/
theorem symmetric_pair_sum_product_dvd {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hs : S f = f) (ν : ℚ) (hν : ν ≠ 0)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = ν • f) :
    (X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2) ∣ f := by
  have h01 : bind₁ (Function.update X (0 : Fin 3) (-X 1)) f = 0 := by
    rw [update_X_zero]
    change value f (-X 1) (X 1) (X 2) = 0
    simpa only [neg_neg] using
      symmetric_opposite_value_zero hf hs ν hν hp (-X (1 : Fin 3)) (X 2)
  have h02 : bind₁ (Function.update X (0 : Fin 3) (-X 2)) f = 0 := by
    rw [update_X_zero]
    change value f (-X 2) (X 1) (X 2) = 0
    rw [value_swap23 hf.1 hs (-X (2 : Fin 3)) (X 2) (X 1)]
    simpa only [neg_neg] using
      symmetric_opposite_value_zero hf hs ν hν hp (-X (2 : Fin 3)) (X 1)
  have h12 : bind₁ (Function.update X (1 : Fin 3) (-X 2)) f = 0 := by
    rw [update_X_one]
    change value f (X 0) (-X 2) (X 2) = 0
    rw [← value_cyclic hf.1 (X (0 : Fin 3)) (-X 2) (X 2)]
    simpa only [neg_neg] using
      symmetric_opposite_value_zero hf hs ν hν hp (-X (2 : Fin 3)) (X 0)
  have hd01 : X 0 + X 1 ∣ f := by
    simpa only [sub_neg_eq_add] using
      linear_factor_dvd_of_substitution_zero f 0 (-X 1) h01
  have hkeep02 : bind₁ (Function.update X (0 : Fin 3) (-X 2)) (X 0 + X 1 : TernaryPolynomial) ≠ 0 := by
    intro h
    have h' := congrArg (eval (![0, 1, 0] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at h'
  have hd02 : (X 0 + X 1) * (X 0 + X 2) ∣ f := by
    simpa only [sub_neg_eq_add] using
      mul_linear_factor_dvd_of_substitution_zero f (X 0 + X 1) 0 (-X 2) hd01 h02 hkeep02
  have hkeep12 : bind₁ (Function.update X (1 : Fin 3) (-X 2))
      ((X 0 + X 1) * (X 0 + X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have h' := congrArg (eval (![1, 0, 0] : Fin 3 → ℚ)) h
    norm_num [update_X_one, Matrix.cons_val_two] at h'
  simpa only [sub_neg_eq_add] using
    mul_linear_factor_dvd_of_substitution_zero f ((X 0 + X 1) * (X 0 + X 2))
      1 (-X 2) hd02 h12 hkeep12

/-- In the even sector the total-coordinate plane supplies an additional factor. -/
theorem symmetric_total_pair_sum_product_dvd {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hs : S f = f)
    (hp : bind₁ ![-X 0, -X 1, -X 2] f = f) :
    (X 0 + X 1 + X 2) * ((X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2)) ∣ f := by
  have hd := symmetric_pair_sum_product_dvd hf hs 1 one_ne_zero (by simpa using hp)
  have hz : bind₁ (Function.update X (0 : Fin 3) (-(X 1 + X 2))) f = 0 := by
    rw [update_X_zero]
    change value f (-(X 1 + X 2)) (X 1) (X 2) = 0
    have harg : - (-(X 1 + X 2) + X 1 : TernaryPolynomial) = X 2 := by abel
    have hzero := symmetric_total_value_zero (σ := Fin 3) hf hs hp
      (-(X 1 + X 2)) (X 1)
    rwa [harg] at hzero
  have hkeep : bind₁ (Function.update X (0 : Fin 3) (-(X 1 + X 2)))
      ((X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2) : TernaryPolynomial) ≠ 0 := by
    intro h
    have h' := congrArg (eval (![0, 1, 1] : Fin 3 → ℚ)) h
    norm_num [update_X_zero, Matrix.cons_val_two] at h'
  have h := mul_linear_factor_dvd_of_substitution_zero f
    ((X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2)) 0 (-(X 1 + X 2)) hd hz hkeep
  rw [mul_comm] at h
  simpa only [sub_neg_eq_add, ← add_assoc] using h

/-- The paper's three-factor divisibility holds in every homogeneous symmetric degree. -/
theorem homogeneous_symmetric_pair_sum_product_dvd {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f = f) (hg : f.IsHomogeneous n) :
    (X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2) ∣ f :=
  symmetric_pair_sum_product_dvd hf hs ((-1 : ℚ) ^ n)
    (pow_ne_zero n (by norm_num)) (homogeneous_bind_neg hg)

/-- In even homogeneous degree all four distinct linear factors divide together. -/
theorem homogeneous_symmetric_total_pair_sum_product_dvd {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f = f) (hg : f.IsHomogeneous n) (hn : Even n) :
    (X 0 + X 1 + X 2) * ((X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2)) ∣ f :=
  symmetric_total_pair_sum_product_dvd hf hs (homogeneous_bind_neg_even hg hn)

end TernaryPoly
