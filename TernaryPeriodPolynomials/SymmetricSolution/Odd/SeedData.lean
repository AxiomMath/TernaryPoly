module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.RationalTower
public import TernaryPeriodPolynomials.SymmetricSolution.SeedData
public import TernaryPeriodPolynomials.SymmetricSolution.FirstJet.Lift

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricOddRationalTower
open SymmetricOddRationalSeed

variable {k : ℕ}

theorem qPolynomial_swap (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i)) :
    S (qPolynomial q hq)=qPolynomial q hq := by
  have hs : S (X 0+X 1)=(X 0+X 1 : TP) := by simp [S,add_comm]
  simp only [qPolynomial,map_sum,map_mul,map_pow,hs,symmetricOddSeedQ_swap]

theorem qPolynomial_odd (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i)) :
    bind₁ ![X 0,X 1,-X 2] (qPolynomial q hq)= -qPolynomial q hq := by
  have ht : bind₁ (![X 0,X 1,-X 2] : Fin 3 → TP) (X 0+X 1 : TP)=X 0+X 1 := by simp
  simp only [qPolynomial,map_sum,map_mul,map_pow,ht,symmetricOddSeedQ_odd,
    mul_neg,Finset.sum_neg_distrib]

/-- Exact first mixed equation for the same Q used by the full rational P tower. -/
theorem qPolynomial_first_mixed (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i) :
    bind₁ ![X 0,X 1,X 2+X 0] (qPolynomial q hq)-qPolynomial q hq=
      bind₁ ![X 0+X 2,-X 2,X 1] (∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i) := by
  have ht : bind₁ (![X 0,X 1,X 2+X 0] : Fin 3 → TP) (X 0+X 1 : TP)=X 0+X 1 := by simp
  have hm : bind₁ (![X 0+X 2,-X 2,X 1] : Fin 3 → TP) (X 0+X 1+X 2 : TP)=X 0+X 1 := by simp
  simp only [qPolynomial,map_sum,map_mul,map_pow,ht,hm,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_sub,symmetricOddSeedQ_mixed _ (hq i) _ (hl i)]

/-- The matching polynomial Q also has its pure norm, with no unproved lift premise. -/
theorem qPolynomial_norm (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (f : TP) (hf : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hrel : PeriodRelations f) (hs : S f=f) : N (qPolynomial q hq)=0 := by
  apply SymmetricFirstLift.norm_zero hrel.1 hs hrel.2
    (qPolynomial_swap q hq) (qPolynomial_odd q hq)
  rw [hf]
  exact qPolynomial_first_mixed q hq l hl

theorem regular_substitute (q : Fin k → BP) (a b c : TP) :
    substitute3 (regular q (X 0) (X 1) (X 2)) a b c=regular q a b c := by
  unfold regular
  simp only [substitute3,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact map_zero _
  · rw [map_mul,map_pow,bind₁_X_right]
    change a^(2*(i:ℕ)-1)*substitute3 (binaryLiftEval (q i) (X 1) (X 2)) a b c=_
    rw [binaryLiftEval_substitute3]
    simp [substitute3]

/-- Once the actual lowest period vanishes, all rational seed equations are polynomial equations. -/
theorem polynomial_data_of_lowest_zero (q : Fin k → BP)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (hzero : lowest q=0) :
    SymmetricSeedData (∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
      (regular q (X 0) (X 1) (X 2)) (qPolynomial q hq) := by
  have he (a b c : TP) (ha : a≠0) : pValue q a b c=embed (regular q a b c) := by
    rw [pValue_split q a b c ha,hzero]
    simp [P,binaryLiftEval]
  have hinj := IsFractionRing.injective TP Frac
  constructor
  · exact qPolynomial_swap q hq
  · exact qPolynomial_odd q hq
  · change substitute3 (regular q (X 0) (X 1) (X 2)) (X 0) (X 2) (X 1)=_
    rw [regular_substitute]
    apply hinj
    rw [←he _ _ _ (X_ne_zero 0),←he _ _ _ (X_ne_zero 0),pValue_swap q hq]
  · change substitute3 (regular q (X 0) (X 1) (X 2)) (X 0) (-X 1) (X 2)=_
    rw [regular_substitute]
    apply hinj
    rw [map_neg,←he _ _ _ (X_ne_zero 0),←he _ _ _ (X_ne_zero 0),pValue_odd_second q hq]
  · change substitute3 (regular q (X 0) (X 1) (X 2)) (X 0) (X 1) (-X 2)=_
    rw [regular_substitute]
    apply hinj
    rw [map_neg,←he _ _ _ (X_ne_zero 0),←he _ _ _ (X_ne_zero 0),pValue_odd_third q hq]
  · change regular q (X 0) (X 1) (X 2)+
        substitute3 (regular q (X 0) (X 1) (X 2)) (X 0) (-X 2) (X 1-X 2)+
        substitute3 (regular q (X 0) (X 1) (X 2)) (X 0) (X 2-X 1) (-X 1)=0
    rw [regular_substitute,regular_substitute]
    apply hinj
    simp only [map_add,map_zero]
    rw [←he _ _ _ (X_ne_zero 0),←he _ _ _ (X_ne_zero 0),←he _ _ _ (X_ne_zero 0)]
    exact pValue_norm q hq _ _ _
  · exact qPolynomial_first_mixed q hq l hl
  · change substitute3 (regular q (X 0) (X 1) (X 2)) (X 0) (X 2+X 0) (X 1)-
        substitute3 (regular q (X 0) (X 1) (X 2)) (X 0) (X 2) (X 1)=
        substitute3 (qPolynomial q hq) (-X 2) (X 0+X 2) (X 1)
    rw [regular_substitute,regular_substitute]
    apply hinj
    rw [map_sub,←he _ _ _ (X_ne_zero 0),←he _ _ _ (X_ne_zero 0)]
    exact pValue_mixed q hq _ _ _ (X_ne_zero 0)

end TernaryPoly.SymmetricOddRationalTower
