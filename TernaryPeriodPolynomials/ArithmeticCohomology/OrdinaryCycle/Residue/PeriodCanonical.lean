module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientParity

@[expose] public section


open MvPolynomial
open scoped DirectSum
noncomputable section
namespace TernaryPoly.OrdinaryResiduePeriod
open SinglePoleCoordinate SinglePoleSupport OrdinaryResidueGeneral OrdinaryResiduePolynomial
open PolynomialGLAction OrdinaryFullCoefficient

/-- Literal cyclic symmetry of the canonical three-pole fraction. -/
theorem representative_cycle (q : BP) (hq : OrdinaryResidueGeneral.SymmetricOdd q) (a b c : TP) :
    OrdinaryResiduePolynomial.representative q b c a = OrdinaryResiduePolynomial.representative q a b c := by
  unfold OrdinaryResiduePolynomial.representative
  rw [eval_swap hq c a,eval_swap hq b a]
  abel

/-- Literal first transposition symmetry of the canonical three-pole fraction. -/
theorem representative_swap (q : BP) (hq : OrdinaryResidueGeneral.SymmetricOdd q) (a b c : TP) :
    OrdinaryResiduePolynomial.representative q b a c = OrdinaryResiduePolynomial.representative q a b c := by
  unfold OrdinaryResiduePolynomial.representative
  rw [eval_swap hq b a]
  abel

/-- The actual canonical single-pole coefficient satisfies the cyclic apartment equation. -/
theorem canonical_cyclic (n : ℕ) (q : BinaryV (n+1)) (hq : OrdinaryResidueGeneral.SymmetricOdd q.val) :
    integralSinglePoleAction n (-1) ReferenceCoefficientMatrices.c (canonicalRepresentative n q) =
      canonicalRepresentative n q := by
  apply Subtype.ext
  change SinglePole.fractionAction (-1) (integralRational ReferenceCoefficientMatrices.c)
    (canonicalRepresentative n q).val = _
  have hc : determinantCharacter (-1) (integralRational ReferenceCoefficientMatrices.c) = 1 :=
    determinantCharacter_cycle
  rw [canonicalRepresentative_literal,SinglePole.fractionAction_apply,
    hc,one_smul,representative_fractionEquiv,
    ReferenceCoefficientMatrices.substitute_c_inverse]
  simp only [TernaryPoly.C,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  exact representative_cycle q.val hq _ _ _

/-- The determinant-inverse twist gives the negative first-transposition apartment equation. -/
theorem canonical_swap (n : ℕ) (q : BinaryV (n+1)) (hq : OrdinaryResidueGeneral.SymmetricOdd q.val) :
    integralSinglePoleAction n (-1) ReferenceCoefficientMatrices.s (canonicalRepresentative n q) =
      -canonicalRepresentative n q := by
  apply Subtype.ext
  change SinglePole.fractionAction (-1) (integralRational ReferenceCoefficientMatrices.s)
    (canonicalRepresentative n q).val = -(canonicalRepresentative n q).val
  have hs : determinantCharacter (-1) (integralRational ReferenceCoefficientMatrices.s) = -1 :=
    determinantCharacter_swap
  rw [canonicalRepresentative_literal,SinglePole.fractionAction_apply,
    hs,representative_fractionEquiv,
    ReferenceCoefficientMatrices.substitute_s_inverse]
  simp only [TernaryPoly.S,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  rw [representative_swap q.val hq]
  exact @neg_one_smul ℚ Frac _ _ (inferInstance : Module ℚ Frac) _

/-- Every actual coordinate sign action fixes the determinant-inverse twisted canonical coefficient. -/
theorem canonical_sign (n : ℕ) (q : BinaryV (n+1)) (hq : OrdinaryResidueGeneral.SymmetricOdd q.val)
    (s : Fin 3 → Bool) :
    integralSinglePoleAction n (-1) (signMatrix s) (canonicalRepresentative n q) =
      canonicalRepresentative n q := by
  apply Subtype.ext
  change SinglePole.fractionAction (-1) (integralRational (signMatrix s))
    (canonicalRepresentative n q).val = _
  rw [canonicalRepresentative_literal,SinglePole.fractionAction_apply,
    determinantCharacter_signMatrix,representative_fractionEquiv,substitute_sign]
  simp only [bind₁_X_right]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    norm_num [h0,h1,h2,OrdinaryResiduePolynomial.representative,
      eval_neg_first hq,eval_neg_second hq,oddSign,signEntry,Fin.prod_univ_three,
      Algebra.smul_def] <;>
    rw [@neg_one_smul ℚ Frac _ _ (inferInstance : Module ℚ Frac)] <;> ring

/-- The actual canonical residue of a binary period satisfies every full apartment relation. -/
theorem canonical_relations (n : ℕ) (q : BinaryV (n+1)) (hq : SymmetricBinaryPeriodRelations q.val) :
    Relations (SinglePole.residueAction n (-1)) (SinglePole.residue n (canonicalRepresentative n q)) where
  signs s := by
    change integralResidueAction n (-1) (OrdinaryApartmentFrames.signFrame s)
      (SinglePole.residue n (canonicalRepresentative n q)) = _
    rw [signFrame_eq_signMatrix,residue_integral_equivariant,canonical_sign n q (of_period hq)]
  cyclic := by
    change integralResidueAction n (-1) ReferenceCoefficientMatrices.c
      (SinglePole.residue n (canonicalRepresentative n q)) = _
    rw [residue_integral_equivariant,canonical_cyclic n q (of_period hq)]
  swap := by
    change integralResidueAction n (-1) ReferenceCoefficientMatrices.s
      (SinglePole.residue n (canonicalRepresentative n q)) = _
    rw [residue_integral_equivariant,canonical_swap n q (of_period hq),map_neg]
  norm := by
    change SinglePole.residue n (canonicalRepresentative n q) +
      integralResidueAction n (-1) ReferenceCoefficientMatrices.a
        (SinglePole.residue n (canonicalRepresentative n q)) +
      integralResidueAction n (-1) (ReferenceCoefficientMatrices.a^2)
        (SinglePole.residue n (canonicalRepresentative n q)) = 0
    rw [←residue_norm]
    exact (canonical_residue_norm_iff n q (of_period hq)).mpr hq

end TernaryPoly.OrdinaryResiduePeriod
