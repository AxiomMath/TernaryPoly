module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberTable

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryRationalFiber
open SymmetricOddRationalSeed SymmetricOddRationalTower
open OrdinaryCovectors OrdinaryCovectorOrbits OrdinaryPolynomialNorm
open OrdinarySeedEquivariance
variable {k : ℕ}

theorem seedValue_sign12 (f : TP) (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (r : Covector) : seedValue f q hq (sign12 r)=fracD12 (seedValue f q hq r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=(fracD12 (0))
    simp only [map_zero]
  · change (pValue q (X 2) (X 0) (X 1))=(fracD12 ((pValue q (X 2) (X 0) (X 1))))
    simp only [fracD12_P]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_second q hq, pValue_odd_third q hq]
  · change -(pValue q (-X 2) (X 0) (X 1))=(fracD12 (-(pValue q (-X 2) (X 0) (X 1))))
    simp only [fracD12_P, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_second q hq, pValue_odd_third q hq]
  · change -(pValue q (-X 1) (X 0) (X 2))=(fracD12 ((pValue q (X 1) (X 0) (X 2))))
    simp only [fracD12_P]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_odd_second q hq]
  · change -(qValue q hq (-X 1) (X 2) (X 0))=(fracD12 ((qValue q hq (X 1) (X 2) (X 0))))
    simp only [fracD12_Q]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_odd_third q hq]
  · change (qValue q hq (-X 1) (-X 2) (X 0))=(fracD12 (-(qValue q hq (X 1) (-X 2) (X 0))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change (pValue q (X 1) (X 0) (X 2))=(fracD12 (-(pValue q (-X 1) (X 0) (X 2))))
    simp only [fracD12_P, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_second q hq]
  · change (qValue q hq (X 1) (X 2) (X 0))=(fracD12 (-(qValue q hq (-X 1) (X 2) (X 0))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change -(qValue q hq (X 1) (-X 2) (X 0))=(fracD12 ((qValue q hq (-X 1) (-X 2) (X 0))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change -(pValue q (-X 0) (X 1) (X 2))=(fracD12 ((pValue q (X 0) (X 1) (X 2))))
    simp only [fracD12_P]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_odd_second q hq]
  · change -(qValue q hq (-X 0) (X 2) (X 1))=(fracD12 ((qValue q hq (X 0) (X 2) (X 1))))
    simp only [fracD12_Q]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_odd_third q hq]
  · change (qValue q hq (-X 0) (-X 2) (X 1))=(fracD12 (-(qValue q hq (X 0) (-X 2) (X 1))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change (qValue q hq (-X 0) (-X 1) (X 2))=(fracD12 ((qValue q hq (X 0) (X 1) (X 2))))
    simp only [fracD12_Q]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (fValue f (-X 0) (-X 1) (X 2))=(fracD12 ((fValue f (X 0) (X 1) (X 2))))
    simp only [fracD12_F]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(fValue f (-X 0) (-X 1) (-X 2))=(fracD12 (-(fValue f (X 0) (X 1) (-X 2))))
    simp only [fracD12_F, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(qValue q hq (-X 0) (X 1) (X 2))=(fracD12 (-(qValue q hq (X 0) (-X 1) (X 2))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(fValue f (-X 0) (X 1) (X 2))=(fracD12 (-(fValue f (X 0) (-X 1) (X 2))))
    simp only [fracD12_F, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (fValue f (-X 0) (X 1) (-X 2))=(fracD12 ((fValue f (X 0) (-X 1) (-X 2))))
    simp only [fracD12_F, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (pValue q (X 0) (X 1) (X 2))=(fracD12 (-(pValue q (-X 0) (X 1) (X 2))))
    simp only [fracD12_P, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_second q hq]
  · change (qValue q hq (X 0) (X 2) (X 1))=(fracD12 (-(qValue q hq (-X 0) (X 2) (X 1))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change -(qValue q hq (X 0) (-X 2) (X 1))=(fracD12 ((qValue q hq (-X 0) (-X 2) (X 1))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change -(qValue q hq (X 0) (-X 1) (X 2))=(fracD12 (-(qValue q hq (-X 0) (X 1) (X 2))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(fValue f (X 0) (-X 1) (X 2))=(fracD12 (-(fValue f (-X 0) (X 1) (X 2))))
    simp only [fracD12_F, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (fValue f (X 0) (-X 1) (-X 2))=(fracD12 ((fValue f (-X 0) (X 1) (-X 2))))
    simp only [fracD12_F, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (qValue q hq (X 0) (X 1) (X 2))=(fracD12 ((qValue q hq (-X 0) (-X 1) (X 2))))
    simp only [fracD12_Q, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (fValue f (X 0) (X 1) (X 2))=(fracD12 ((fValue f (-X 0) (-X 1) (X 2))))
    simp only [fracD12_F, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(fValue f (X 0) (X 1) (-X 2))=(fracD12 (-(fValue f (-X 0) (-X 1) (-X 2))))
    simp only [fracD12_F, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]

/-- All table entries obey the determinant sign in the actual D3 coefficient symmetry. -/
theorem seedValue_sign3 (f : TP) (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (r : Covector) : seedValue f q hq (sign3 r)= -fracD3 (seedValue f q hq r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=-(fracD3 (0))
    simp only [map_zero,neg_zero]
  · change -(pValue q (-X 2) (X 0) (X 1))=-(fracD3 ((pValue q (X 2) (X 0) (X 1))))
    simp only [fracD3_P]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (pValue q (X 2) (X 0) (X 1))=-(fracD3 (-(pValue q (-X 2) (X 0) (X 1))))
    simp only [fracD3_P, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (pValue q (X 1) (X 0) (X 2))=-(fracD3 ((pValue q (X 1) (X 0) (X 2))))
    simp only [fracD3_P]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_third q hq]
  · change -(qValue q hq (X 1) (-X 2) (X 0))=-(fracD3 ((qValue q hq (X 1) (X 2) (X 0))))
    simp only [fracD3_Q]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (qValue q hq (X 1) (X 2) (X 0))=-(fracD3 (-(qValue q hq (X 1) (-X 2) (X 0))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(pValue q (-X 1) (X 0) (X 2))=-(fracD3 (-(pValue q (-X 1) (X 0) (X 2))))
    simp only [fracD3_P, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_third q hq]
  · change (qValue q hq (-X 1) (-X 2) (X 0))=-(fracD3 (-(qValue q hq (-X 1) (X 2) (X 0))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(qValue q hq (-X 1) (X 2) (X 0))=-(fracD3 ((qValue q hq (-X 1) (-X 2) (X 0))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (pValue q (X 0) (X 1) (X 2))=-(fracD3 ((pValue q (X 0) (X 1) (X 2))))
    simp only [fracD3_P]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_third q hq]
  · change -(qValue q hq (X 0) (-X 2) (X 1))=-(fracD3 ((qValue q hq (X 0) (X 2) (X 1))))
    simp only [fracD3_Q]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (qValue q hq (X 0) (X 2) (X 1))=-(fracD3 (-(qValue q hq (X 0) (-X 2) (X 1))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (qValue q hq (X 0) (X 1) (X 2))=-(fracD3 ((qValue q hq (X 0) (X 1) (X 2))))
    simp only [fracD3_Q]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change -(fValue f (X 0) (X 1) (-X 2))=-(fracD3 ((fValue f (X 0) (X 1) (X 2))))
    simp only [fracD3_F]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (fValue f (X 0) (X 1) (X 2))=-(fracD3 (-(fValue f (X 0) (X 1) (-X 2))))
    simp only [fracD3_F, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(qValue q hq (X 0) (-X 1) (X 2))=-(fracD3 (-(qValue q hq (X 0) (-X 1) (X 2))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change (fValue f (X 0) (-X 1) (-X 2))=-(fracD3 (-(fValue f (X 0) (-X 1) (X 2))))
    simp only [fracD3_F, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(fValue f (X 0) (-X 1) (X 2))=-(fracD3 ((fValue f (X 0) (-X 1) (-X 2))))
    simp only [fracD3_F, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(pValue q (-X 0) (X 1) (X 2))=-(fracD3 (-(pValue q (-X 0) (X 1) (X 2))))
    simp only [fracD3_P, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, pValue_odd_third q hq]
  · change (qValue q hq (-X 0) (-X 2) (X 1))=-(fracD3 (-(qValue q hq (-X 0) (X 2) (X 1))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(qValue q hq (-X 0) (X 2) (X 1))=-(fracD3 ((qValue q hq (-X 0) (-X 2) (X 1))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(qValue q hq (-X 0) (X 1) (X 2))=-(fracD3 (-(qValue q hq (-X 0) (X 1) (X 2))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change (fValue f (-X 0) (X 1) (-X 2))=-(fracD3 (-(fValue f (-X 0) (X 1) (X 2))))
    simp only [fracD3_F, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(fValue f (-X 0) (X 1) (X 2))=-(fracD3 ((fValue f (-X 0) (X 1) (-X 2))))
    simp only [fracD3_F, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (qValue q hq (-X 0) (-X 1) (X 2))=-(fracD3 ((qValue q hq (-X 0) (-X 1) (X 2))))
    simp only [fracD3_Q, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, qValue_odd_third q hq]
  · change -(fValue f (-X 0) (-X 1) (-X 2))=-(fracD3 ((fValue f (-X 0) (-X 1) (X 2))))
    simp only [fracD3_F, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (fValue f (-X 0) (-X 1) (X 2))=-(fracD3 (-(fValue f (-X 0) (-X 1) (-X 2))))
    simp only [fracD3_F, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]


theorem seedValue_swap (f : TP) (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (hs : S f=f) (r : Covector) :
    seedValue f q hq (swapRow r)=fracS (seedValue f q hq r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=fracS (0)
    simp only [map_zero]
  · change (pValue q (X 2) (X 0) (X 1))=fracS ((pValue q (X 2) (X 0) (X 1)))
    simp only [fracS_P]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_swap q hq]
  · change -(pValue q (-X 2) (X 0) (X 1))=fracS (-(pValue q (-X 2) (X 0) (X 1)))
    simp only [fracS_P,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_swap q hq]
  · change (pValue q (X 0) (X 1) (X 2))=fracS ((pValue q (X 1) (X 0) (X 2)))
    simp only [fracS_P]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (qValue q hq (X 0) (X 2) (X 1))=fracS ((qValue q hq (X 1) (X 2) (X 0)))
    simp only [fracS_Q]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(qValue q hq (X 0) (-X 2) (X 1))=fracS (-(qValue q hq (X 1) (-X 2) (X 0)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(pValue q (-X 0) (X 1) (X 2))=fracS (-(pValue q (-X 1) (X 0) (X 2)))
    simp only [fracS_P,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(qValue q hq (-X 0) (X 2) (X 1))=fracS (-(qValue q hq (-X 1) (X 2) (X 0)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (qValue q hq (-X 0) (-X 2) (X 1))=fracS ((qValue q hq (-X 1) (-X 2) (X 0)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (pValue q (X 1) (X 0) (X 2))=fracS ((pValue q (X 0) (X 1) (X 2)))
    simp only [fracS_P]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (qValue q hq (X 1) (X 2) (X 0))=fracS ((qValue q hq (X 0) (X 2) (X 1)))
    simp only [fracS_Q]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(qValue q hq (X 1) (-X 2) (X 0))=fracS (-(qValue q hq (X 0) (-X 2) (X 1)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (qValue q hq (X 0) (X 1) (X 2))=fracS ((qValue q hq (X 0) (X 1) (X 2)))
    simp only [fracS_Q]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change (fValue f (X 0) (X 1) (X 2))=fracS ((fValue f (X 0) (X 1) (X 2)))
    simp only [fracS_F]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]
  · change -(fValue f (X 0) (X 1) (-X 2))=fracS (-(fValue f (X 0) (X 1) (-X 2)))
    simp only [fracS_F,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]
  · change -(qValue q hq (-X 0) (X 1) (X 2))=fracS (-(qValue q hq (X 0) (-X 1) (X 2)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change -(fValue f (-X 0) (X 1) (X 2))=fracS (-(fValue f (X 0) (-X 1) (X 2)))
    simp only [fracS_F,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]
  · change (fValue f (-X 0) (X 1) (-X 2))=fracS ((fValue f (X 0) (-X 1) (-X 2)))
    simp only [fracS_F,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]
  · change -(pValue q (-X 1) (X 0) (X 2))=fracS (-(pValue q (-X 0) (X 1) (X 2)))
    simp only [fracS_P,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(qValue q hq (-X 1) (X 2) (X 0))=fracS (-(qValue q hq (-X 0) (X 2) (X 1)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (qValue q hq (-X 1) (-X 2) (X 0))=fracS ((qValue q hq (-X 0) (-X 2) (X 1)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(qValue q hq (X 0) (-X 1) (X 2))=fracS (-(qValue q hq (-X 0) (X 1) (X 2)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change -(fValue f (X 0) (-X 1) (X 2))=fracS (-(fValue f (-X 0) (X 1) (X 2)))
    simp only [fracS_F,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]
  · change (fValue f (X 0) (-X 1) (-X 2))=fracS ((fValue f (-X 0) (X 1) (-X 2)))
    simp only [fracS_F,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]
  · change (qValue q hq (-X 0) (-X 1) (X 2))=fracS ((qValue q hq (-X 0) (-X 1) (X 2)))
    simp only [fracS_Q,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change (fValue f (-X 0) (-X 1) (X 2))=fracS ((fValue f (-X 0) (-X 1) (X 2)))
    simp only [fracS_F,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]
  · change -(fValue f (-X 0) (-X 1) (-X 2))=fracS (-(fValue f (-X 0) (-X 1) (-X 2)))
    simp only [fracS_F,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs]

/-- The full table obeys the literal cycle permutation coefficient equation. -/
theorem seedValue_cycle (f : TP) (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (hc : C f=f) (hs : S f=f) (r : Covector) :
    seedValue f q hq (cycleRow r)=fracC (seedValue f q hq r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=fracC (0)
    simp only [map_zero]
  · change (pValue q (X 0) (X 1) (X 2))=fracC ((pValue q (X 2) (X 0) (X 1)))
    simp only [fracC_P]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(pValue q (-X 0) (X 1) (X 2))=fracC (-(pValue q (-X 2) (X 0) (X 1)))
    simp only [fracC_P,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (pValue q (X 2) (X 0) (X 1))=fracC ((pValue q (X 1) (X 0) (X 2)))
    simp only [fracC_P]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_swap q hq]
  · change (qValue q hq (X 0) (X 2) (X 1))=fracC ((qValue q hq (X 1) (X 2) (X 0)))
    simp only [fracC_Q]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change -(qValue q hq (-X 0) (X 2) (X 1))=fracC (-(qValue q hq (X 1) (-X 2) (X 0)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change -(pValue q (-X 2) (X 0) (X 1))=fracC (-(pValue q (-X 1) (X 0) (X 2)))
    simp only [fracC_P,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_swap q hq]
  · change -(qValue q hq (X 0) (-X 2) (X 1))=fracC (-(qValue q hq (-X 1) (X 2) (X 0)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change (qValue q hq (-X 0) (-X 2) (X 1))=fracC ((qValue q hq (-X 1) (-X 2) (X 0)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change (pValue q (X 1) (X 0) (X 2))=fracC ((pValue q (X 0) (X 1) (X 2)))
    simp only [fracC_P]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_swap q hq]
  · change (qValue q hq (X 0) (X 1) (X 2))=fracC ((qValue q hq (X 0) (X 2) (X 1)))
    simp only [fracC_Q]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change -(qValue q hq (-X 0) (X 1) (X 2))=fracC (-(qValue q hq (X 0) (-X 2) (X 1)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change (qValue q hq (X 1) (X 2) (X 0))=fracC ((qValue q hq (X 0) (X 1) (X 2)))
    simp only [fracC_Q]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (fValue f (X 0) (X 1) (X 2))=fracC ((fValue f (X 0) (X 1) (X 2)))
    simp only [fracC_F]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]
  · change -(fValue f (-X 0) (X 1) (X 2))=fracC (-(fValue f (X 0) (X 1) (-X 2)))
    simp only [fracC_F,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]
  · change -(qValue q hq (X 1) (-X 2) (X 0))=fracC (-(qValue q hq (X 0) (-X 1) (X 2)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(fValue f (X 0) (X 1) (-X 2))=fracC (-(fValue f (X 0) (-X 1) (X 2)))
    simp only [fracC_F,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]
  · change (fValue f (-X 0) (X 1) (-X 2))=fracC ((fValue f (X 0) (-X 1) (-X 2)))
    simp only [fracC_F,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]
  · change -(pValue q (-X 1) (X 0) (X 2))=fracC (-(pValue q (-X 0) (X 1) (X 2)))
    simp only [fracC_P,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pValue_swap q hq]
  · change -(qValue q hq (X 0) (-X 1) (X 2))=fracC (-(qValue q hq (-X 0) (X 2) (X 1)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change (qValue q hq (-X 0) (-X 1) (X 2))=fracC ((qValue q hq (-X 0) (-X 2) (X 1)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, qValue_swap q hq]
  · change -(qValue q hq (-X 1) (X 2) (X 0))=fracC (-(qValue q hq (-X 0) (X 1) (X 2)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(fValue f (X 0) (-X 1) (X 2))=fracC (-(fValue f (-X 0) (X 1) (X 2)))
    simp only [fracC_F,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]
  · change (fValue f (-X 0) (-X 1) (X 2))=fracC ((fValue f (-X 0) (X 1) (-X 2)))
    simp only [fracC_F,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]
  · change (qValue q hq (-X 1) (-X 2) (X 0))=fracC ((qValue q hq (-X 0) (-X 1) (X 2)))
    simp only [fracC_Q,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (fValue f (X 0) (-X 1) (-X 2))=fracC ((fValue f (-X 0) (-X 1) (X 2)))
    simp only [fracC_F,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]
  · change -(fValue f (-X 0) (-X 1) (-X 2))=fracC (-(fValue f (-X 0) (-X 1) (-X 2)))
    simp only [fracC_F,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, fValue_swap hs, fValue_swap_last hc hs]


end TernaryPoly.OrdinaryRationalFiber
