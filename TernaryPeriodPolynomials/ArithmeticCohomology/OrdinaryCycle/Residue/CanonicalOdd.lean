module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.CanonicalLift

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueGeneral
open OrdinaryResiduePolynomial SinglePoleCoordinate SinglePoleSupport PolynomialGLAction

/-- The actual sign matrix negating only the first ternary coordinate. -/
def firstCoordinateSign : Fin 3 → Bool := ![true,false,false]

@[simp] theorem oddSign_firstCoordinateSign : oddSign firstCoordinateSign= -1 := by
  simp [oddSign,signEntry,firstCoordinateSign,Fin.prod_univ_three]

theorem substitute_firstCoordinateSign :
    substitute ((integralRational (signMatrix firstCoordinateSign))⁻¹ : GL3)=
      bind₁ ![-X 0,X 1,X 2] := by
  rw [substitute_sign]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Literal first-coordinate oddness of the three-pole representative. -/
theorem representative_neg_first (q : BP) (hq : SymmetricOdd q) (a b c : TP) :
    representative q (-a) b c= -representative q a b c := by
  simp only [representative,eval_neg_first hq,map_neg,div_neg,neg_div]
  ring

/-- The actual first-coordinate rational matrix acts by minus one on the canonical representative. -/
theorem representative_firstCoordinateSign (q : BP) (hq : SymmetricOdd q) :
    SinglePole.fractionEquiv (integralRational (signMatrix firstCoordinateSign))
      (representative q (X 0) (X 1) (X 2))=
      -representative q (X 0) (X 1) (X 2) := by
  rw [representative_fractionEquiv,substitute_firstCoordinateSign]
  simp only [bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  exact representative_neg_first q hq _ _ _

/-- The determinant twist cancels from the stated actual separate-oddness equations. -/
theorem fraction_first_odd_of_singlePole (n : ℕ) (e : ℤ) (x : SinglePole.singlePole n)
    (hodd : ∀ s, integralSinglePoleAction n e (signMatrix s) x =
      (determinantCharacter e (integralRational (signMatrix s))*oddSign s) • x) :
    SinglePole.fractionEquiv (integralRational (signMatrix firstCoordinateSign)) x.val= -x.val := by
  have he := congrArg Subtype.val (hodd firstCoordinateSign)
  change determinantCharacter e (integralRational (signMatrix firstCoordinateSign)) •
    SinglePole.fractionEquiv (integralRational (signMatrix firstCoordinateSign)) x.val=
    (determinantCharacter e (integralRational (signMatrix firstCoordinateSign))*
      oddSign firstCoordinateSign) • x.val at he
  rw [oddSign_firstCoordinateSign,mul_neg_one] at he
  have hs : (-(determinantCharacter e (integralRational (signMatrix firstCoordinateSign))) : ℚ) • x.val=
      determinantCharacter e (integralRational (signMatrix firstCoordinateSign)) • (-x.val) :=
    (neg_smul (determinantCharacter e (integralRational (signMatrix firstCoordinateSign))) x.val).trans
      (@smul_neg ℚ Frac _ (inferInstance : Module ℚ Frac).toDistribMulAction.toDistribSMul
        (determinantCharacter e (integralRational (signMatrix firstCoordinateSign))) x.val).symm
  exact (smul_right_injective Frac (determinantCharacter_ne_zero e _)) (he.trans hs)

/-- The actual homogeneous polynomial correction inherits the required literal first oddness. -/
theorem correction_odd_first (q : BP) (hq : SymmetricOdd q) (x : Frac) (p : TP)
    (hx : SinglePole.fractionEquiv (integralRational (signMatrix firstCoordinateSign)) x= -x)
    (hp : x=representative q (X 0) (X 1) (X 2)+embed p) :
    bind₁ ![-X 0,X 1,X 2] p= -p := by
  rw [hp,map_add,representative_firstCoordinateSign q hq,SinglePole.fractionEquiv_embed,
    substitute_firstCoordinateSign] at hx
  apply IsFractionRing.injective TP Frac
  rw [map_neg]
  linear_combination hx

/-- Every actual symmetric separately odd norm-zero single-pole coefficient has
zero extreme coefficient in its homogeneous binary coordinate period. -/
theorem exists_period_lift_extreme (n : ℕ) (e : ℤ) (x : SinglePole.singlePole n)
    (hsym : ∀ π, integralSinglePoleAction n e (permutationMatrix π) x =
      determinantCharacter e (integralRational (permutationMatrix π)) • x)
    (hodd : ∀ s, integralSinglePoleAction n e (signMatrix s) x =
      (determinantCharacter e (integralRational (signMatrix s))*oddSign s) • x)
    (hnorm : x+integralSinglePoleAction n e ReferenceCoefficientMatrices.a x+
      integralSinglePoleAction n e (ReferenceCoefficientMatrices.a^2) x=0) :
    ∃ q : BinaryV (n+1), ∃ p : SinglePole.V n,
      SymmetricBinaryPeriodRelations q.val ∧
      x.val=representative q.val (X 0) (X 1) (X 2)+embed p.val ∧
      bind₁ ![-X 0,X 1,X 2] p.val= -p.val ∧
      ∀ m : Fin 1 →₀ ℕ,q.val.coeff (Finsupp.cons 1 m)=0 := by
  obtain ⟨q,p,hq,hp,hn⟩ := exists_period_polynomial_correction n e x hsym hodd hnorm
  have ho := correction_odd_first q.val (of_period hq) x.val p.val
    (fraction_first_odd_of_singlePole n e x hodd) hp
  exact ⟨q,p,hq,hp,ho,fun m => OrdinaryResidueExtreme.extreme_coefficient_zero q.val hq p.val ho hn m⟩

end TernaryPoly.OrdinaryResidueGeneral
