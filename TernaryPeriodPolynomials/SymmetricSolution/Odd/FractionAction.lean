module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.RationalTower
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Action

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricOddRationalTower
open SymmetricOddRationalSeed PolynomialGLAction

variable {k : ℕ}

theorem substitute_binaryLiftEval (M : Matrix (Fin 3) (Fin 3) ℚ) (q : BP) (a b : TP) :
    substitute M (binaryLiftEval q a b)=binaryLiftEval q (substitute M a) (substitute M b) := by
  have hv : (fun i : Fin 2 => substitute M ((![a,b] : Fin 2 → TP) i))=
      ![substitute M a,substitute M b] := by
    funext i
    fin_cases i <;> rfl
  simp only [binaryLiftEval,substitute,bind₁_bind₁]
  change bind₁ (fun i : Fin 2 => substitute M ((![a,b] : Fin 2 → TP) i)) q=_
  rw [hv]
  rfl

theorem substitute_numerator (M : Matrix (Fin 3) (Fin 3) ℚ) (q : Fin k → BP) (a b c : TP) :
    substitute M (numerator q a b c)=
      numerator q (substitute M a) (substitute M b) (substitute M c) := by
  simp only [numerator,map_sum,map_mul,map_pow,substitute_binaryLiftEval]

/-- Rational coordinate formulas are transported by the genuine fraction-field action. -/
theorem pValue_fractionEquiv (g : GL3) (q : Fin k → BP) (a b c : TP) :
    SinglePole.fractionEquiv g (pValue q a b c)=
      pValue q (substitute (g⁻¹ : GL3) a) (substitute (g⁻¹ : GL3) b)
        (substitute (g⁻¹ : GL3) c) := by
  simp only [pValue,map_div₀,SinglePole.fractionEquiv_embed,substitute_numerator]

/-- The determinant character remains explicit on every rational seed placement. -/
theorem pValue_fractionAction (e : ℤ) (g : GL3) (q : Fin k → BP) (a b c : TP) :
    SinglePole.fractionAction e g (pValue q a b c)=
      determinantCharacter e g • pValue q (substitute (g⁻¹ : GL3) a)
        (substitute (g⁻¹ : GL3) b) (substitute (g⁻¹ : GL3) c) := by
  rw [SinglePole.fractionAction_apply,pValue_fractionEquiv]

end TernaryPoly.SymmetricOddRationalTower
