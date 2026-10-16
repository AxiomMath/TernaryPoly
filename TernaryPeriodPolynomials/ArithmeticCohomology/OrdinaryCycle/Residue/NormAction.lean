module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.GeneralNorm
public import TernaryPeriodPolynomials.SymmetricSolution.Odd.FractionAction
public import TernaryPeriodPolynomials.Building.Reference.CoefficientMatrices

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueGeneral
open OrdinaryResiduePolynomial PolynomialGLAction ReferenceCoefficientMatrices

/-- The actual determinant-twisted order-three norm on the fraction field. -/
def fractionNorm (e : ℤ) (x : Frac) : Frac :=
  x+SinglePole.fractionAction e (rational a) x+SinglePole.fractionAction e (rational (a^2)) x

theorem representative_fractionEquiv (g : GL3) (q : BP) (u v w : TP) :
    SinglePole.fractionEquiv g (representative q u v w)=
      representative q (substitute (g⁻¹ : GL3) u) (substitute (g⁻¹ : GL3) v)
        (substitute (g⁻¹ : GL3) w) := by
  simp only [representative,map_add,map_div₀,SinglePole.fractionEquiv_embed,
    SymmetricOddRationalTower.substitute_binaryLiftEval]

private theorem char_a (e : ℤ) : determinantCharacter e (rational a)=1 := by
  have hd : Matrix.GeneralLinearGroup.det (rational a)=1 := by
    rw [Matrix.GeneralLinearGroup.map_det,det_a,map_one]
  change ((Matrix.GeneralLinearGroup.det (rational a) : ℚˣ) : ℚ)^e=1
  rw [hd]
  simp

private theorem char_a_sq (e : ℤ) : determinantCharacter e (rational (a^2))=1 := by
  rw [map_pow,map_pow,char_a,pow_two,mul_one]

private theorem substitute_a_sq_inverse : substitute ((rational (a^2))⁻¹ : GL3)=A := by
  apply DFunLike.ext
  intro p
  have h := coefficientAction_a_sq 0 p
  change action 0 (rational (a^2)) p=A p at h
  change ((Matrix.GeneralLinearGroup.det (rational (a^2)) : ℚˣ) : ℚ)^(0 : ℤ) •
    substitute ((rational (a^2))⁻¹ : GL3) p=A p at h
  simpa only [zpow_zero,one_smul] using h

/-- The literal rational calculation agrees with the genuine inverse-substitution group norm. -/
theorem fractionNorm_representative (e : ℤ) (q : BP) :
    fractionNorm e (representative q (X 0) (X 1) (X 2))=representativeNorm q := by
  simp only [fractionNorm,SinglePole.fractionAction_apply,char_a,char_a_sq,one_smul,
    representative_fractionEquiv,substitute_a_inverse,substitute_a_sq_inverse]
  simp only [A,A2,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,representativeNorm]
  abel

/-- On embedded polynomials the genuine fraction-field norm is the norm. -/
theorem fractionNorm_embed (e : ℤ) (p : TP) : fractionNorm e (embed p)=embed (N p) := by
  simp only [fractionNorm,SinglePole.fractionAction_embed]
  change embed p+embed (coefficientAction e a p)+embed (coefficientAction e (a^2) p)=embed (N p)
  rw [coefficientAction_a,coefficientAction_a_sq]
  simp only [N_apply,map_add]
  abel

theorem fractionNorm_add (e : ℤ) (x y : Frac) :
    fractionNorm e (x+y)=fractionNorm e x+fractionNorm e y := by
  simp only [fractionNorm,map_add]
  abel

/-- An actual norm-zero rational lift forces the complete binary period relation. -/
theorem period_of_norm_zero_lift (e : ℤ) (q : BP) (h : SymmetricOdd q) (p : TP)
    (hn : fractionNorm e (representative q (X 0) (X 1) (X 2)+embed p)=0) :
    SymmetricBinaryPeriodRelations q := by
  apply (representativeNorm_polynomial_iff q h).mp
  refine ⟨-N p,?_⟩
  rw [fractionNorm_add,fractionNorm_representative,fractionNorm_embed] at hn
  rw [map_neg]
  linear_combination -hn

end TernaryPoly.OrdinaryResidueGeneral
