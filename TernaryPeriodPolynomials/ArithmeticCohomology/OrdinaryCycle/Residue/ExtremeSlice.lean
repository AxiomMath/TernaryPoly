module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Polynomial
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueExtreme
open OrdinaryResiduePolynomial

abbrev Coeff := MvPolynomial (Fin 1) ℚ
abbrev SlicePoly := Polynomial Coeff

/-- The literal specialization (a,b,c)=(X,-X,c), retaining c as a polynomial coefficient. -/
def slice : TernaryPolynomial →ₐ[ℚ] SlicePoly :=
  aeval ![Polynomial.X,-Polynomial.X,Polynomial.C (X 0)]

@[simp] lemma slice_X_zero : slice (X 0)=Polynomial.X := by simp [slice]
@[simp] lemma slice_X_one : slice (X 1)= -Polynomial.X := by simp [slice]
@[simp] lemma slice_X_two : slice (X 2)=Polynomial.C (X 0) := by simp [slice]

lemma split_X_one : finSuccEquiv ℚ 1 (X (1 : Fin 2))=Polynomial.C (X 0) :=
  finSuccEquiv_X_succ (j := 0)

/-- Binary evaluation in the first and third variables is the literal finSucc polynomial. -/
lemma slice_binary (q : BP) (p : TernaryPolynomial) :
    slice (binaryLiftEval q p (X 2))=(finSuccEquiv ℚ 1 q).comp (slice p) := by
  induction q using MvPolynomial.induction_on with
  | C r => simp [binaryLiftEval,slice,finSuccEquiv_apply]
  | add q r hq hr =>
    simp only [binaryLiftEval,map_add,Polynomial.add_comp] at *
    rw [hq,hr]
  | mul_X q i hq =>
    simp only [binaryLiftEval,map_mul,bind₁_X_right,Polynomial.mul_comp] at *
    rw [hq]
    fin_cases i
    · simp [finSuccEquiv_X_zero]
    · simp [split_X_one]

lemma split_odd (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    (finSuccEquiv ℚ 1 q).comp (-Polynomial.X)= -(finSuccEquiv ℚ 1 q) := by
  have he := congrArg slice (symmetricBinaryEval_neg_first hq (X 0) (X 2))
  simpa only [slice_binary,map_neg,slice_X_zero,Polynomial.comp_X] using he

/-- The exact three numerator terms after b=-a, with the literal binary polynomial. -/
lemma slice_numerator (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    slice (numerator q)=
      Polynomial.C 2*Polynomial.X^2*(finSuccEquiv ℚ 1 q)-
      Polynomial.C 4*Polynomial.X^2*((finSuccEquiv ℚ 1 q).comp (Polynomial.C 2*Polynomial.X)) := by
  simp only [numerator,map_sub,map_mul,map_pow,slice_binary,slice_X_zero,slice_X_one,
    Polynomial.comp_X,split_odd q hq]
  have he : (Polynomial.X- -Polynomial.X : SlicePoly)=Polynomial.C 2*Polynomial.X := by
    simp only [map_ofNat]
    ring
  rw [he]
  simp only [map_ofNat]
  ring

lemma slice_denominator : slice denominator=Polynomial.C (-2)*Polynomial.X^3 := by
  simp only [denominator,map_mul,map_sub,slice_X_zero,slice_X_one,map_neg,map_ofNat]
  ring

/-- The actual numerator divisibility identity specializes with no formal division step. -/
lemma slice_defect_identity (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    Polynomial.C (-2)*Polynomial.X^3*slice (defect q hq)=
      Polynomial.C 2*Polynomial.X^2*(finSuccEquiv ℚ 1 q)-
      Polynomial.C 4*Polynomial.X^2*((finSuccEquiv ℚ 1 q).comp (Polynomial.C 2*Polynomial.X)) := by
  have he := congrArg slice (numerator_eq q hq)
  rw [map_mul,slice_denominator,slice_numerator q hq] at he
  exact he.symm

/-- The constant slice coefficient is exactly three times the literal first binary coefficient. -/
theorem defect_slice_coeff_zero (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    (slice (defect q hq)).coeff 0=3*(finSuccEquiv ℚ 1 q).coeff 1 := by
  have he := congrArg (fun p : SlicePoly => p.coeff 3) (slice_defect_identity q hq)
  simp only [mul_assoc,Polynomial.coeff_C_mul,Polynomial.coeff_sub,
    Polynomial.coeff_X_pow_mul',Polynomial.comp_C_mul_X_coeff] at he
  norm_num at he
  apply mul_left_cancel₀ (show (2 : Coeff)≠0 by norm_num)
  linear_combination -he

end TernaryPoly.OrdinaryResidueExtreme
