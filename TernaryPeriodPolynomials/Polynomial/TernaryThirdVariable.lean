module

public import TernaryPeriodPolynomials.Polynomial.Operators
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Transport
public import TernaryPeriodPolynomials.Polynomial.TripleDifference
public import Mathlib.Tactic.LinearCombination

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.TernaryThirdVariable

abbrev Binary := MvPolynomial (Fin 2) ℚ

/-- Regard the third coordinate as the polynomial variable and the first two as coefficients. -/
def toPoly : TernaryPolynomial →ₐ[ℚ] Polynomial Binary :=
  (finSuccEquiv ℚ 2).toAlgHom.comp TernaryPoly.C

@[simp] theorem toPoly_X_zero : toPoly (X 0)=Polynomial.C (X 0) := by
  simp [toPoly,TernaryPoly.C,finSuccEquiv_ternary_X_one]

@[simp] theorem toPoly_X_one : toPoly (X 1)=Polynomial.C (X 1) := by
  simp [toPoly,TernaryPoly.C,finSuccEquiv_ternary_X_two]

@[simp] theorem toPoly_X_two : toPoly (X 2)=Polynomial.X := by
  simp [toPoly,TernaryPoly.C,finSuccEquiv_X_zero]

theorem toPoly_injective : Function.Injective toPoly := by
  intro f g h
  have he : TernaryPoly.C f=TernaryPoly.C g := (finSuccEquiv ℚ 2).injective h
  have hh := congrArg (fun p => TernaryPoly.C (TernaryPoly.C p)) he
  simpa only [C_C_C] using hh

/-- Substituting the third coordinate becomes literal univariate composition. -/
theorem toPoly_bind_third (f c : TernaryPolynomial) :
    toPoly (bind₁ ![X 0,X 1,c] f)=(toPoly f).comp (toPoly c) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [toPoly,TernaryPoly.C,finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,hp,hq,Polynomial.add_comp]
  | mul_X p i hp =>
    simp only [map_mul,hp,Polynomial.mul_comp]
    fin_cases i <;> simp

/-- Oddness in the third coordinate is preserved by the exact coordinate equivalence. -/
theorem toPoly_odd {f : TernaryPolynomial}
    (h : bind₁ ![X 0,X 1,-X 2] f= -f) :
    (toPoly f).comp (-Polynomial.X)= -toPoly f := by
  have he := congrArg toPoly h
  simpa only [toPoly_bind_third,map_neg,toPoly_X_two] using he

/-- The nonzero first-coordinate specialization is the corresponding univariate root. -/
theorem toPoly_eval_zero {f : TernaryPolynomial}
    (h : bind₁ ![X 0,X 1,X 0] f=(0 : TernaryPolynomial)) :
    (toPoly f).eval (X 0)=0 := by
  have he := congrArg toPoly h
  rw [toPoly_bind_third,toPoly_X_zero,Polynomial.comp_C,map_zero] at he
  exact Polynomial.C_injective (by simpa only [map_zero] using he)

/-- Exact transport of the three translation differences used by the first lift. -/
theorem toPoly_triple_difference {f : TernaryPolynomial}
    (h : bind₁ ![X 0,X 1,X 2+X 0+(-X 1)+(X 1-X 0)] f
      -bind₁ ![X 0,X 1,X 2+X 0+(-X 1)] f
      -bind₁ ![X 0,X 1,X 2+X 0+(X 1-X 0)] f
      +bind₁ ![X 0,X 1,X 2+X 0] f
      -bind₁ ![X 0,X 1,X 2+(-X 1)+(X 1-X 0)] f
      +bind₁ ![X 0,X 1,X 2+(-X 1)] f
      +bind₁ ![X 0,X 1,X 2+(X 1-X 0)] f
      -bind₁ ![X 0,X 1,X 2] f=(0 : TernaryPolynomial)) :
    PolynomialTripleDifference.difference (X 0)
      (PolynomialTripleDifference.difference (-X 1)
        (PolynomialTripleDifference.difference (X 1-X 0) (toPoly f)))=0 := by
  have he := congrArg toPoly h
  simp only [map_add,map_sub,map_neg,map_zero,toPoly_bind_third,
    toPoly_X_zero,toPoly_X_one,toPoly_X_two] at he
  simp only [PolynomialTripleDifference.difference,map_sub,Polynomial.taylor_taylor]
  simp only [Polynomial.taylor_apply,map_add,map_sub,map_neg,add_assoc,Polynomial.comp_X] at he ⊢
  linear_combination he

end TernaryPoly.TernaryThirdVariable
