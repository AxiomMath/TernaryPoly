module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.ExtremeSlice
public import Mathlib.Algebra.Ring.CharZero

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueExtreme
open OrdinaryResiduePolynomial

/-- The literal c-axis substitution, retaining the full polynomial dependence on c. -/
def axis : TernaryPolynomial →ₐ[ℚ] Coeff := aeval ![0,0,X 0]

lemma axis_substitute (P : TernaryPolynomial) (a b c : TernaryPolynomial) :
    axis (bind₁ ![a,b,c] P)=aeval ![axis a,axis b,axis c] P := by
  rw [axis,aeval_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- Setting the slice variable to zero is literally setting a=b=0. -/
lemma slice_coeff_zero (P : TernaryPolynomial) : (slice P).coeff 0=axis P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [slice,axis]
  | add P Q hP hQ => simp only [map_add,Polynomial.coeff_add,hP,hQ]
  | mul_X P i hP =>
    simp only [map_mul,Polynomial.mul_coeff_zero,hP]
    fin_cases i <;> simp [slice,axis]

/-- Oddness in just the first coordinate forces the literal c-axis value to vanish. -/
lemma axis_zero_of_odd_first (P : TernaryPolynomial)
    (hodd : bind₁ ![-X 0,X 1,X 2] P= -P) : axis P=0 := by
  have he := congrArg axis hodd
  rw [axis_substitute,map_neg] at he
  have ht : axis P= -axis P := by simpa [axis] using he
  exact CharZero.eq_neg_self_iff.mp ht

lemma axis_A (P : TernaryPolynomial) : axis (A P)=axis P := by
  change axis (bind₁ ![-X 1,X 0-X 1,X 2] P)=axis P
  rw [axis_substitute]
  simp [axis]

lemma axis_A2 (P : TernaryPolynomial) : axis (A2 P)=axis P := by
  change axis (bind₁ ![X 1-X 0,-X 0,X 2] P)=axis P
  rw [axis_substitute]
  simp [axis]

lemma axis_norm (P : TernaryPolynomial) : axis (N P)=3*axis P := by
  rw [N_apply,map_add,map_add,axis_A,axis_A2]
  ring

/-- An actual first-odd polynomial lift annihilates the full defect value on the c-axis. -/
lemma defect_axis_zero (q : BP) (hq : SymmetricBinaryPeriodRelations q)
    (P : TernaryPolynomial) (hodd : bind₁ ![-X 0,X 1,X 2] P= -P)
    (hlift : N P= -defect q hq) : axis (defect q hq)=0 := by
  have he := congrArg axis hlift
  rw [axis_norm,axis_zero_of_odd_first P hodd,mul_zero,map_neg] at he
  exact neg_eq_zero.mp he.symm

/-- The entire coefficient polynomial of the first binary power vanishes; no degree bound is used. -/
theorem first_coefficient_zero (q : BP) (hq : SymmetricBinaryPeriodRelations q)
    (P : TernaryPolynomial) (hodd : bind₁ ![-X 0,X 1,X 2] P= -P)
    (hlift : N P= -defect q hq) : (finSuccEquiv ℚ 1 q).coeff 1=0 := by
  have he := defect_slice_coeff_zero q hq
  rw [slice_coeff_zero,defect_axis_zero q hq P hodd hlift] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- The literal binary coefficient [a c^m] is zero for every exponent, with no homogeneity premise. -/
theorem extreme_coefficient_zero (q : BP) (hq : SymmetricBinaryPeriodRelations q)
    (P : TernaryPolynomial) (hodd : bind₁ ![-X 0,X 1,X 2] P= -P)
    (hlift : N P= -defect q hq) (m : Fin 1 →₀ ℕ) :
    q.coeff (Finsupp.cons 1 m)=0 := by
  rw [← finSuccEquiv_coeff_coeff m q 1,first_coefficient_zero q hq P hodd hlift,AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The paper's specified monomial a*c^n is the same literal coefficient. -/
theorem extreme_coefficient_nat_zero (q : BP) (hq : SymmetricBinaryPeriodRelations q)
    (P : TernaryPolynomial) (hodd : bind₁ ![-X 0,X 1,X 2] P= -P)
    (hlift : N P= -defect q hq) (n : ℕ) :
    q.coeff (Finsupp.single 0 1+Finsupp.single 1 n)=0 := by
  have hm : Finsupp.cons 1 (Finsupp.single (0 : Fin 1) n)=
      Finsupp.single (0 : Fin 2) 1+Finsupp.single 1 n := by
    ext i
    fin_cases i
    · simp
    · change (Finsupp.cons 1 (Finsupp.single (0 : Fin 1) n)) (Fin.succ 0)=_
      rw [Finsupp.cons_succ]
      simp
  rw [← hm]
  exact extreme_coefficient_zero q hq P hodd hlift _

end TernaryPoly.OrdinaryResidueExtreme
