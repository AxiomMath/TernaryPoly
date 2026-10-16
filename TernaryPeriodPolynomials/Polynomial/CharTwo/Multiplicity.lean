module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Projector
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Data.Fintype.Order
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm
open CharTwoProjector (sub Symmetric)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem four_eq_zero : (4 : Poly) = 0 := by
  have h : (4 : Poly) = (2 : Poly)+2 := by norm_num
  simpa only [CharTwo.two_eq_zero (R := Poly), add_zero] using h

/-- In characteristic two the elementary polynomial `ab+c` is the three diagonal factors. -/
theorem cplus_eq_product : cplus = (X 0+X 1)*(X 0+X 2)*(X 1+X 2) := by
  unfold cplus a b c
  ring_nf
  simp [four_eq_zero, CharTwo.two_eq_zero (R := Poly)]

/-- A symmetric norm-zero polynomial vanishes whenever its first two arguments coincide. -/
theorem norm_zero_diagonal {f : Poly} (hs : Symmetric f) (hn : norm f = 0)
    (u v : Poly) : sub f u u v = 0 := by
  have h := CharTwoProjector.sub_norm_zero hn u u v
  rw [CharTwo.add_self_eq_zero, CharTwoProjector.sub_swap hs u 0 v] at h
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using h

/-- The three diagonal planes all vanish, including arbitrary polynomial values. -/
theorem norm_zero_diagonals {f : Poly} (hs : Symmetric f) (hn : norm f = 0)
    (u v : Poly) : sub f u u v = 0 ∧ sub f u v u = 0 ∧ sub f v u u = 0 := by
  refine ⟨norm_zero_diagonal hs hn u v, ?_, ?_⟩
  · rw [CharTwoProjector.sub_cycle hs u u v]
    exact norm_zero_diagonal hs hn u v
  · rw [CharTwoProjector.sub_swap hs u v u]
    rw [CharTwoProjector.sub_cycle hs u u v]
    exact norm_zero_diagonal hs hn u v

/-- The sum plane also vanishes, by the exact norm equation and the diagonal planes. -/
theorem norm_zero_sum_plane {f : Poly} (hs : Symmetric f) (hn : norm f = 0)
    (u v : Poly) : sub f (u+v) u v = 0 := by
  have h := CharTwoProjector.sub_norm_zero hn (u+v) u v
  have hu : (u+v)+u = v := by
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  rw [hu, (norm_zero_diagonals hs hn v u).2.2,
    (norm_zero_diagonals hs hn v (u+v)).2.1, add_zero, add_zero] at h
  exact h

private theorem form01_ne_zero : (X 0-X 1 : Poly) ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ZMod 2)) h
  norm_num [Matrix.cons_val_two] at he

private theorem form02_ne_zero : (X 0-X 2 : Poly) ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ZMod 2)) h
  norm_num [Matrix.cons_val_two] at he

private theorem form12_ne_zero : (X 1-X 2 : Poly) ≠ 0 := by
  intro h
  have he := congrArg (eval (![0,1,0] : Fin 3 → ZMod 2)) h
  norm_num [Matrix.cons_val_two] at he

/-- The entire symmetric norm kernel has the four distinct plane factors `a*(ab+c)`. -/
theorem a_cplus_dvd_of_norm_zero {f : Poly} (hs : Symmetric f) (hn : norm f = 0) :
    a*cplus ∣ f := by
  have h01 : bind₁ (Function.update (X : Fin 3 → Poly) 0 (X 1)) f = 0 := by
    have hv : Function.update (X : Fin 3 → Poly) 0 (X 1) = ![X 1,X 1,X 2] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact norm_zero_diagonal hs hn (X 1) (X 2)
  have h02 : bind₁ (Function.update (X : Fin 3 → Poly) 0 (X 2)) f = 0 := by
    have hv : Function.update (X : Fin 3 → Poly) 0 (X 2) = ![X 2,X 1,X 2] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact (norm_zero_diagonals hs hn (X 2) (X 1)).2.1
  have h12 : bind₁ (Function.update (X : Fin 3 → Poly) 1 (X 2)) f = 0 := by
    have hv : Function.update (X : Fin 3 → Poly) 1 (X 2) = ![X 0,X 2,X 2] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact (norm_zero_diagonals hs hn (X 2) (X 0)).2.2
  have hsum : bind₁ (Function.update (X : Fin 3 → Poly) 0 (X 1+X 2)) f = 0 := by
    have hv : Function.update (X : Fin 3 → Poly) 0 (X 1+X 2) = ![X 1+X 2,X 1,X 2] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact norm_zero_sum_plane hs hn (X 1) (X 2)
  have hd1 := linear_factor_dvd_of_substitution_zero f 0 (X 1) h01
  have hd2 := mul_linear_factor_dvd_of_substitution_zero f (X 0-X 1) 0 (X 2) hd1 h02
    (by simpa [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using form12_ne_zero)
  have hd3 := mul_linear_factor_dvd_of_substitution_zero f ((X 0-X 1)*(X 0-X 2)) 1 (X 2)
    hd2 h12 (by simpa using mul_ne_zero form02_ne_zero form02_ne_zero)
  have hkeep : bind₁ (Function.update (X : Fin 3 → Poly) 0 (X 1+X 2))
      ((X 0-X 1)*(X 0-X 2)*(X 1-X 2)) ≠ 0 := by
    simpa using mul_ne_zero (mul_ne_zero (X_ne_zero (2 : Fin 3)) (X_ne_zero (1 : Fin 3))) form12_ne_zero
  have hd4 := mul_linear_factor_dvd_of_substitution_zero f
    ((X 0-X 1)*(X 0-X 2)*(X 1-X 2)) 0 (X 1+X 2) hd3 hsum hkeep
  convert hd4 using 1
  rw [cplus_eq_product]
  simp only [a, sub_eq_add_neg, CharTwo.neg_eq]
  ring

end TernaryPoly.CharTwoNorm
