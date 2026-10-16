module

public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Fraction

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower OrdinaryRationalFiber
open OrdinaryCovectors OrdinaryPolynomialNorm

/-- The separately odd projection, with its exact rational normalization. -/
def oddProjection (f : TP) : TP := (1/8 : ℚ) •
  (substitute3 f (X 0) (X 1) (X 2)-substitute3 f (X 0) (X 1) (-X 2)-
   substitute3 f (X 0) (-X 1) (X 2)+substitute3 f (X 0) (-X 1) (-X 2)-
   substitute3 f (-X 0) (X 1) (X 2)+substitute3 f (-X 0) (X 1) (-X 2)+
   substitute3 f (-X 0) (-X 1) (X 2)-substitute3 f (-X 0) (-X 1) (-X 2))

/-- The three cyclic placements of a polynomial. -/
def cyclicPolynomial (f : TP) : TP := f+C f+C (C f)

/-- The three cyclic placements of the rational support-one seed. -/
def cyclicP {k : ℕ} (q : Fin k → BP) : Frac :=
  pValue q (X 0) (X 1) (X 2)+pValue q (X 1) (X 2) (X 0)+pValue q (X 2) (X 0) (X 1)

theorem bind_vector (a b c x y z : TP) :
    (fun i => bind₁ ![a,b,c] (![x,y,z] i))=
      ![bind₁ ![a,b,c] x,bind₁ ![a,b,c] y,bind₁ ![a,b,c] z] := by
  funext i
  fin_cases i <;> rfl

/-- Evaluation of the odd projection is the actual eight-term sign average. -/
theorem fValue_oddProjection (f a b c : TP) :
    fValue (oddProjection f) a b c=(1/8 : ℚ) •
      (fValue f a b c-fValue f a b (-c)-fValue f a (-b) c+fValue f a (-b) (-c)-
       fValue f (-a) b c+fValue f (-a) b (-c)+fValue f (-a) (-b) c-fValue f (-a) (-b) (-c)) := by
  simp [oddProjection,fValue,substitute3,map_rat_smul,bind₁_bind₁,bind_vector]

theorem fValue_cyclicPolynomial (f a b c : TP) :
    fValue (cyclicPolynomial f) a b c=fValue f a b c+fValue f b c a+fValue f c a b := by
  simp [cyclicPolynomial,fValue,C,substitute3,bind₁_bind₁,bind_vector]

/-- The27 covectors have their literal three-coordinate product parametrization. -/
def covectorProduct : Covector ≃ ZMod 3 × ZMod 3 × ZMod 3 where
  toFun r := (r 0,r 1,r 2)
  invFun t := ![t.1,t.2.1,t.2.2]
  left_inv r := by funext i; fin_cases i <;> rfl
  right_inv t := by rcases t with ⟨a,b,c⟩; rfl

theorem sum_covectors (F : Covector → Frac) :
    (∑ r : Covector,F r)=∑ a : ZMod 3,∑ b : ZMod 3,∑ c : ZMod 3,F ![a,b,c] := by
  have he := Fintype.sum_equiv covectorProduct F
    (fun t : ZMod 3 × ZMod 3 × ZMod 3 => F ![t.1,t.2.1,t.2.2])
    (fun r => congrArg F (covectorProduct.left_inv r).symm)
  simpa only [Fintype.sum_prod_type] using he

theorem sum_zmod_three (F : ZMod 3 → Frac) : (∑ r : ZMod 3,F r)=F 0+F 1+F 2 :=
  Fin.sum_univ_three F

variable {k : ℕ}

theorem rat_smul_eq_mul (c : ℚ) (x : Frac) : c • x=(c : Frac)*x := by
  have he := ratCast_smul_eq ℚ Frac c x
  simpa only [Rat.cast_id,smul_eq_mul] using he

/-- Literal support-size decomposition, retaining all polynomial terms. -/
theorem trace_support_decomposition (f : TP) (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i)) :
    trace f q hq=2*cyclicP q+
      4*embed (cyclicPolynomial (oddProjection (qPolynomial q hq)))+
      8*embed (oddProjection f) := by
  unfold trace
  rw [fiberTrace_eq_sum _ (by rfl),sum_covectors]
  rw [←fValue_self (cyclicPolynomial (oddProjection (qPolynomial q hq))),
    fValue_cyclicPolynomial,←fValue_self (oddProjection f)]
  simp only [sum_zmod_three]
  change ((0+(pValue q (X 2) (X 0) (X 1))+-(pValue q (-X 2) (X 0) (X 1)))+
        ((pValue q (X 1) (X 0) (X 2))+(qValue q hq (X 1) (X 2) (X 0))+-(qValue q hq (X 1) (-X 2) (X 0)))+
        (-(pValue q (-X 1) (X 0) (X 2))+-(qValue q hq (-X 1) (X 2) (X 0))+(qValue q hq (-X 1) (-X 2) (X 0)))) +
      (((pValue q (X 0) (X 1) (X 2))+(qValue q hq (X 0) (X 2) (X 1))+-(qValue q hq (X 0) (-X 2) (X 1)))+
        ((qValue q hq (X 0) (X 1) (X 2))+(fValue f (X 0) (X 1) (X 2))+-(fValue f (X 0) (X 1) (-X 2)))+
        (-(qValue q hq (X 0) (-X 1) (X 2))+-(fValue f (X 0) (-X 1) (X 2))+(fValue f (X 0) (-X 1) (-X 2)))) +
      ((-(pValue q (-X 0) (X 1) (X 2))+-(qValue q hq (-X 0) (X 2) (X 1))+(qValue q hq (-X 0) (-X 2) (X 1)))+
        (-(qValue q hq (-X 0) (X 1) (X 2))+-(fValue f (-X 0) (X 1) (X 2))+(fValue f (-X 0) (X 1) (-X 2)))+
        ((qValue q hq (-X 0) (-X 1) (X 2))+(fValue f (-X 0) (-X 1) (X 2))+-(fValue f (-X 0) (-X 1) (-X 2)))) = _
  simp only [fValue_oddProjection]
  change _ = 2*cyclicP q+4*((1/8 : ℚ) •
      (qValue q hq (X 0) (X 1) (X 2)-qValue q hq (X 0) (X 1) (-X 2)-
       qValue q hq (X 0) (-X 1) (X 2)+qValue q hq (X 0) (-X 1) (-X 2)-
       qValue q hq (-X 0) (X 1) (X 2)+qValue q hq (-X 0) (X 1) (-X 2)+
       qValue q hq (-X 0) (-X 1) (X 2)-qValue q hq (-X 0) (-X 1) (-X 2))+
    (1/8 : ℚ) •
      (qValue q hq (X 1) (X 2) (X 0)-qValue q hq (X 1) (X 2) (-X 0)-
       qValue q hq (X 1) (-X 2) (X 0)+qValue q hq (X 1) (-X 2) (-X 0)-
       qValue q hq (-X 1) (X 2) (X 0)+qValue q hq (-X 1) (X 2) (-X 0)+
       qValue q hq (-X 1) (-X 2) (X 0)-qValue q hq (-X 1) (-X 2) (-X 0))+
    (1/8 : ℚ) •
      (qValue q hq (X 2) (X 0) (X 1)-qValue q hq (X 2) (X 0) (-X 1)-
       qValue q hq (X 2) (-X 0) (X 1)+qValue q hq (X 2) (-X 0) (-X 1)-
       qValue q hq (-X 2) (X 0) (X 1)+qValue q hq (-X 2) (X 0) (-X 1)+
       qValue q hq (-X 2) (-X 0) (X 1)-qValue q hq (-X 2) (-X 0) (-X 1)))+_
  simp only [qValue_odd_third,pValue_odd_first,cyclicP]
  rw [pValue_swap q hq (X 1) (X 2) (X 0)]
  rw [qValue_swap q hq (X 0) (X 2) (X 1),
    qValue_swap q hq (-X 0) (X 2) (X 1),
    qValue_swap q hq (X 0) (-X 2) (X 1),
    qValue_swap q hq (-X 0) (-X 2) (X 1)]
  simp only [rat_smul_eq_mul]
  norm_num
  ring

/-- The polynomial part of the three support-one seeds. -/
def cyclicRegular (q : Fin k → BP) : TP :=
  regular q (X 0) (X 1) (X 2)+regular q (X 1) (X 2) (X 0)+regular q (X 2) (X 0) (X 1)

/-- The explicit polynomial correction includes the regular tower, Q and f contributions. -/
def polynomialCorrection (f : TP) (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i)) : TP :=
  2*cyclicRegular q+4*cyclicPolynomial (oddProjection (qPolynomial q hq))+8*oddProjection f

theorem cyclicP_split (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i)) :
    cyclicP q=OrdinaryResiduePolynomial.representative (lowest q) (X 0) (X 1) (X 2)+
      embed (cyclicRegular q) := by
  rw [cyclicP,pValue_split q (X 0) (X 1) (X 2) (X_ne_zero 0),
    pValue_split q (X 1) (X 2) (X 0) (X_ne_zero 1),
    pValue_split q (X 2) (X 0) (X 1) (X_ne_zero 2)]
  have he : P (lowest q) (X 1) (X 2) (X 0)=P (lowest q) (X 1) (X 0) (X 2) := by
    unfold P
    congr 2
    simp only [lowest,binaryLiftEval,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · exact symmetricBinaryEval_swap (hq i) (X 0) (X 2)
    · simp only [map_zero]
  rw [he]
  simp only [OrdinaryResiduePolynomial.representative,P,cyclicRegular,map_add]
  ring

/-- Exact equality in the actual fraction field, with the polynomial correction exposed. -/
theorem trace_residue_correction (f : TP) (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i)) :
    trace f q hq=2*OrdinaryResiduePolynomial.representative (lowest q) (X 0) (X 1) (X 2)+
      embed (polynomialCorrection f q hq) := by
  rw [trace_support_decomposition,cyclicP_split q hq]
  simp only [polynomialCorrection,map_add,map_mul,map_ofNat]
  ring

end TernaryPoly.SymmetricRationalTrace
