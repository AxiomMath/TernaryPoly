module

public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.Basic
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.GroupTheory.Perm.Option

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryApolar
open BinaryHomogeneous
variable (K : Type*) [Field K]

/-- The literal d-th power of a binary linear form. -/
def pure (d : ℕ) (a b : K) : H K d :=
  ⟨(C a * X 0 + C b * X 1)^d,by
    simpa using ((isHomogeneous_C_mul_X a (0 : Fin 2)).add
      (isHomogeneous_C_mul_X b 1)).pow d⟩

/-- The actual coefficient formula for powers of binary linear forms. -/
theorem coordinates_pure (d : ℕ) (a b : K) (i : Fin (d+1)) :
    coordinates K d (pure K d a b) i = (d.choose i.val : K)*a^i.val*b^(d-i.val) := by
  change ((C a*X 0+C b*X 1 : MvPolynomial (Fin 2) K)^d).coeff (exponent d i)=_
  have hlin : (C a*X 0+C b*X 1 : MvPolynomial (Fin 2) K) =
      ∑ j : Fin 2, (![a,b] : Fin 2 → K) j • X j := by
    simp [Fin.sum_univ_two,smul_eq_C_mul]
  rw [hlin,coeff_linearCombination_X_pow_of_fintype]
  have hdeg : (exponent d i).sum (fun _ m => m)=d := exponent_degree d i
  rw [ite_eq_left hdeg,Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _),
    Finset.univ_fin2,Nat.binomial_eq_choose Fin.zero_ne_one]
  rw [Finsupp.prod_fintype _ _ (by intro j; simp)]
  simp only [exponent_zero,exponent_one,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]
  ring

/-- Evaluation is the literal finite coefficient sum. -/
theorem eval_coordinates (d : ℕ) (p : H K d) (a b : K) :
    eval ![a,b] p.val = ∑ i : Fin (d+1),coordinates K d p i*a^i.val*b^(d-i.val) := by
  have hp := congrArg Subtype.val (polynomial_coordinates K d p)
  rw [← hp]
  change eval ![a,b] (∑ i,monomial (exponent d i) (coordinates K d p i))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [monomial_fin_two,exponent_zero,exponent_one]

/-- Apolar testing against a pure power evaluates the other polynomial at the rotated vector. -/
theorem form_pure [CharZero K] (d : ℕ) (p : H K d) (a b : K) :
    form K d p (pure K d a b)=eval ![-b,a] p.val := by
  rw [form_apply,value,eval_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinates_pure]
  have hi : i.rev.val=d-i.val := by simp [Fin.rev]
  have hdi : d-(d-i.val)=i.val := by omega
  rw [hi,hdi,Nat.choose_symm (Nat.le_of_lt_succ i.isLt)]
  have hc : (d.choose i.val : K) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)).ne'
  simp only [weight]
  rw [neg_pow b i.val]
  field_simp

/-- On pure powers the pairing is the d-th power of the two-by-two determinant. -/
theorem form_pure_pure [CharZero K] (d : ℕ) (a b c e : K) :
    form K d (pure K d a b) (pure K d c e)=(b*c-a*e)^d := by
  rw [form_pure]
  change eval ![-e,c] ((C a*X 0+C b*X 1)^d)=_
  simp only [map_pow,map_add,map_mul,eval_C,eval_X,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  congr 1
  ring

end TernaryPoly.BinaryApolar
