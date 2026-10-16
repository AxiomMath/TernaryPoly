module

public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodLift
public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResiduePolynomial

abbrev BP := MvPolynomial (Fin 2) ℚ
abbrev TP := TernaryPolynomial

/-- The exact numerator of the polynomial defect of the symmetric single-pole representative. -/
def numerator (q : BP) : TP :=
  X 0^2*binaryLiftEval q (X 0) (X 2) - X 1^2*binaryLiftEval q (X 1) (X 2) -
    (X 0-X 1)^2*binaryLiftEval q (X 0-X 1) (X 2)

def denominator : TP := X 0*X 1*(X 0-X 1)

private theorem bind_binary (q : BP) (x y a b c : TP) :
    bind₁ ![a,b,c] (binaryLiftEval q x y)=
      binaryLiftEval q (bind₁ ![a,b,c] x) (bind₁ ![a,b,c] y) := by
  exact binaryLiftEval_substitute3 q x y a b c

private theorem numerator_substitute (q : BP) (a b c : TP) :
    substitute3 (numerator q) a b c =
      a^2*binaryLiftEval q a c-b^2*binaryLiftEval q b c-
        (a-b)^2*binaryLiftEval q (a-b) c := by
  simp only [numerator,substitute3,map_sub,map_mul,map_pow,bind_binary,
    bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

private theorem update_zero : Function.update (X : Fin 3 → TP) 0 0 = ![0,X 1,X 2] := by
  funext i
  fin_cases i <;> simp
private theorem update_one : Function.update (X : Fin 3 → TP) 1 0 = ![X 0,0,X 2] := by
  funext i
  fin_cases i <;> simp
private theorem update_diagonal : Function.update (X : Fin 3 → TP) 0 (X 1) = ![X 1,X 1,X 2] := by
  funext i
  fin_cases i <;> simp

private theorem numerator_zero (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ (Function.update X 0 (0 : TP)) (numerator q)=0 := by
  rw [update_zero]
  change substitute3 (numerator q) 0 (X 1) (X 2)=0
  rw [numerator_substitute]
  rw [zero_sub,symmetricBinaryEval_neg_first hq]
  ring

private theorem numerator_one (q : BP) :
    bind₁ (Function.update X 1 (0 : TP)) (numerator q)=0 := by
  rw [update_one]
  change substitute3 (numerator q) (X 0) 0 (X 2)=0
  rw [numerator_substitute]
  simp

private theorem numerator_diagonal (q : BP) :
    bind₁ (Function.update X 0 (X 1 : TP)) (numerator q)=0 := by
  rw [update_diagonal]
  change substitute3 (numerator q) (X 1) (X 1) (X 2)=0
  rw [numerator_substitute]
  simp

/-- All three distinct linear denominator factors cancel, without a bound on the degree. -/
theorem denominator_dvd (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    denominator ∣ numerator q := by
  have h0 : (X 0 : TP) ∣ numerator q := by
    simpa only [sub_zero] using linear_factor_dvd_of_substitution_zero
      (numerator q) 0 0 (numerator_zero q hq)
  have h1 : (X 0*X 1 : TP) ∣ numerator q := by
    have h := mul_linear_factor_dvd_of_substitution_zero (numerator q) (X 0) 1 0 h0
      (numerator_one q) (by simpa only [update_one,bind₁_X_right,Matrix.cons_val_zero]
        using (X_ne_zero (R := ℚ) (0 : Fin 3)))
    simpa only [sub_zero] using h
  apply mul_linear_factor_dvd_of_substitution_zero (numerator q) (X 0*X 1) 0 (X 1)
    h1 (numerator_diagonal q)
  simpa only [update_diagonal,map_mul,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one]
    using mul_ne_zero (X_ne_zero (R := ℚ) (1 : Fin 3)) (X_ne_zero (R := ℚ) (1 : Fin 3))

/-- The polynomial defect with exactly the denominator normalization used by the residue argument. -/
def defect (q : BP) (hq : SymmetricBinaryPeriodRelations q) : TP :=
  Classical.choose (denominator_dvd q hq)

theorem numerator_eq (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    numerator q=denominator*defect q hq := Classical.choose_spec (denominator_dvd q hq)

end TernaryPoly.OrdinaryResiduePolynomial
