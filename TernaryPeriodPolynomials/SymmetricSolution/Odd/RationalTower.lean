module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.RationalSeed

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricOddRationalTower
open SymmetricOddRationalSeed

variable {k : ℕ}

def numerator (q : Fin k → BP) (a b c : TP) : TP :=
  ∑ i : Fin k, a^(2*(i:ℕ))*binaryLiftEval (q i) b c

def pValue (q : Fin k → BP) (a b c : TP) : Frac := embed (numerator q a b c)/embed a

def qPolynomial (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i)) : TP :=
  ∑ i : Fin k, (X 0+X 1)^(2*(i:ℕ))*symmetricOddSeedQ (q i) (hq i)

def lowest (q : Fin k → BP) : BP := ∑ i : Fin k, if (i:ℕ)=0 then q i else 0

def regular (q : Fin k → BP) (a b c : TP) : TP :=
  ∑ i : Fin k, if (i:ℕ)=0 then 0 else a^(2*(i:ℕ)-1)*binaryLiftEval (q i) b c

theorem pValue_sum (q : Fin k → BP) (a b c : TP) :
    pValue q a b c=∑ i : Fin k, embed a^(2*(i:ℕ))*P (q i) a b c := by
  simp only [pValue,numerator,map_sum,Finset.sum_div,map_mul,map_pow,P,mul_div_assoc]

theorem qPolynomial_substitute (q : Fin k → BP)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i)) (a b c : TP) :
    substitute3 (qPolynomial q hq) a b c=∑ i : Fin k,(a+b)^(2*(i:ℕ))*Q (q i) (hq i) a b c := by
  simp only [qPolynomial,substitute3,map_sum,map_mul,map_pow,map_add,bind₁_X_right,
    Matrix.cons_val_zero,Matrix.cons_val_one,Q]

theorem pValue_swap (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (a b c : TP) : pValue q a c b=pValue q a b c := by
  simp only [pValue_sum,P_swap _ (hq _)]

theorem pValue_odd_second (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (a b c : TP) : pValue q a (-b) c= -pValue q a b c := by
  simp only [pValue_sum,P_odd_second _ (hq _),mul_neg,Finset.sum_neg_distrib]

theorem pValue_odd_third (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (a b c : TP) : pValue q a b (-c)= -pValue q a b c := by
  simp only [pValue_sum,P_odd_third _ (hq _),mul_neg,Finset.sum_neg_distrib]

theorem pValue_odd_first (q : Fin k → BP) (a b c : TP) :
    pValue q (-a) b c= -pValue q a b c := by
  simp only [pValue_sum,map_neg,Even.neg_pow (even_two_mul _),P_odd_first,
    mul_neg,Finset.sum_neg_distrib]

/-- Every layer, including the lowest pole, satisfies the exact second mixed equation. -/
theorem pValue_mixed (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (a b c : TP) (ha : a≠0) :
    pValue q a (c+a) b-pValue q a c b=embed (substitute3 (qPolynomial q hq) (-c) (a+c) b) := by
  rw [pValue_sum,pValue_sum,←Finset.sum_sub_distrib,qPolynomial_substitute]
  simp only [show -c+(a+c)=a by ring,map_sum,map_mul,map_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_sub,P_mixed _ (hq i) _ _ _ ha]

theorem pValue_norm (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (a b c : TP) :
    pValue q a b c+pValue q a (-c) (b-c)+pValue q a (c-b) (-b)=0 := by
  simp only [pValue_sum,←Finset.sum_add_distrib,←mul_add,P_norm _ (hq _),mul_zero,
    Finset.sum_const_zero]

/-- All nonlowest layers are polynomial after division by the first coordinate. -/
theorem numerator_split (q : Fin k → BP) (a b c : TP) :
    numerator q a b c=a*regular q a b c+binaryLiftEval (lowest q) b c := by
  simp only [numerator,regular,lowest,binaryLiftEval,map_sum,Finset.mul_sum,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · simp [hi]
  · simp only [map_zero,add_zero]
    have he : 2*(i:ℕ)=1+(2*(i:ℕ)-1) := by omega
    conv_lhs => rw [he,pow_add,pow_one]
    rw [mul_assoc]

/-- Literal sole-pole decomposition, valid for every finite tower. -/
theorem pValue_split (q : Fin k → BP) (a b c : TP) (ha : a≠0) :
    pValue q a b c=embed (regular q a b c)+P (lowest q) a b c := by
  have ha' : embed a≠0 := by simpa only [map_zero] using (IsFractionRing.injective TP Frac).ne ha
  rw [pValue,numerator_split,map_add,map_mul,add_div,mul_div_cancel_left₀ _ ha',P]

/-- The pole vanishes precisely when the lowest period vanishes; higher periods are unrestricted. -/
theorem pValue_polynomial_iff (q : Fin k → BP) :
    (∃ r : TP,embed r=pValue q (X 0) (X 1) (X 2)) ↔ lowest q=0 := by
  rw [pValue_split _ _ _ _ (X_ne_zero 0)]
  constructor
  · rintro ⟨r,hr⟩
    apply (P_polynomial_iff (lowest q)).mp
    refine ⟨r-regular q (X 0) (X 1) (X 2),?_⟩
    rw [map_sub,hr,add_sub_cancel_left]
  · intro h
    obtain ⟨r,hr⟩ := (P_polynomial_iff (lowest q)).mpr h
    exact ⟨regular q (X 0) (X 1) (X 2)+r,by rw [map_add,hr]⟩

end TernaryPoly.SymmetricOddRationalTower
