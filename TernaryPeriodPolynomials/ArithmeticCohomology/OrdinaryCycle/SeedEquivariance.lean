module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.SeedFibers
public import TernaryPeriodPolynomials.SymmetricSolution.ToddCertificate

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinarySeedEquivariance
open OrdinaryCovectors OrdinarySeedFibers

/-- Right row action of the first-coordinate transposition. -/
def swapRow (r : Covector) : Covector := ![r 1,r 0,r 2]
/-- Right row action of the inverse cyclic matrix, matching C. -/
def cycleRow (r : Covector) : Covector := ![r 2,r 0,r 1]

private theorem P_swap {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) : substitute3 P a c b=substitute3 P a b c := by
  have he := congrArg (fun t => substitute3 t a b c) h.p_swap
  change substitute3 (substitute3 P (X 0) (X 2) (X 1)) a b c=substitute3 P a b c at he
  rw [substitute3_substitute3] at he
  simpa [substitute3] using he

private theorem Q_swap {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) : substitute3 Q b a c=substitute3 Q a b c := by
  have he := congrArg (fun t => substitute3 t a b c) h.q_swap
  change substitute3 (substitute3 Q (X 1) (X 0) (X 2)) a b c=substitute3 Q a b c at he
  rw [substitute3_substitute3] at he
  simpa [substitute3] using he

private theorem S_substitute (g a b c : TernaryPolynomial) :
    S (substitute3 g a b c)=substitute3 g (S a) (S b) (S c) :=
  substitute3_substitute3 g a b c (X 1) (X 0) (X 2)
private theorem C_substitute (g a b c : TernaryPolynomial) :
    C (substitute3 g a b c)=substitute3 g (C a) (C b) (C c) :=
  substitute3_substitute3 g a b c (X 1) (X 2) (X 0)

/-- The full table obeys the literal swap permutation coefficient equation. -/
theorem seedValue_swap {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (hs : S f=f) (r : Covector) :
    seedValue f P Q (swapRow r)=S (seedValue f P Q r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=S (0)
    simp only [map_zero]
  · change (substitute3 P (X 2) (X 0) (X 1))=S ((substitute3 P (X 2) (X 0) (X 1)))
    simp only [S_substitute]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_swap h]
  · change -(substitute3 P (-X 2) (X 0) (X 1))=S (-(substitute3 P (-X 2) (X 0) (X 1)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_swap h]
  · change (substitute3 P (X 0) (X 1) (X 2))=S ((substitute3 P (X 1) (X 0) (X 2)))
    simp only [S_substitute]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 Q (X 0) (X 2) (X 1))=S ((substitute3 Q (X 1) (X 2) (X 0)))
    simp only [S_substitute]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 Q (X 0) (-X 2) (X 1))=S (-(substitute3 Q (X 1) (-X 2) (X 0)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 P (-X 0) (X 1) (X 2))=S (-(substitute3 P (-X 1) (X 0) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 Q (-X 0) (X 2) (X 1))=S (-(substitute3 Q (-X 1) (X 2) (X 0)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 Q (-X 0) (-X 2) (X 1))=S ((substitute3 Q (-X 1) (-X 2) (X 0)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 P (X 1) (X 0) (X 2))=S ((substitute3 P (X 0) (X 1) (X 2)))
    simp only [S_substitute]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 Q (X 1) (X 2) (X 0))=S ((substitute3 Q (X 0) (X 2) (X 1)))
    simp only [S_substitute]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 Q (X 1) (-X 2) (X 0))=S (-(substitute3 Q (X 0) (-X 2) (X 1)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 Q (X 0) (X 1) (X 2))=S ((substitute3 Q (X 0) (X 1) (X 2)))
    simp only [S_substitute]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change (substitute3 f (X 0) (X 1) (X 2))=S ((substitute3 f (X 0) (X 1) (X 2)))
    simp only [S_substitute]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]
  · change -(substitute3 f (X 0) (X 1) (-X 2))=S (-(substitute3 f (X 0) (X 1) (-X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]
  · change -(substitute3 Q (-X 0) (X 1) (X 2))=S (-(substitute3 Q (X 0) (-X 1) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change -(substitute3 f (-X 0) (X 1) (X 2))=S (-(substitute3 f (X 0) (-X 1) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]
  · change (substitute3 f (-X 0) (X 1) (-X 2))=S ((substitute3 f (X 0) (-X 1) (-X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]
  · change -(substitute3 P (-X 1) (X 0) (X 2))=S (-(substitute3 P (-X 0) (X 1) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 Q (-X 1) (X 2) (X 0))=S (-(substitute3 Q (-X 0) (X 2) (X 1)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 Q (-X 1) (-X 2) (X 0))=S ((substitute3 Q (-X 0) (-X 2) (X 1)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 Q (X 0) (-X 1) (X 2))=S (-(substitute3 Q (-X 0) (X 1) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change -(substitute3 f (X 0) (-X 1) (X 2))=S (-(substitute3 f (-X 0) (X 1) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]
  · change (substitute3 f (X 0) (-X 1) (-X 2))=S ((substitute3 f (-X 0) (X 1) (-X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]
  · change (substitute3 Q (-X 0) (-X 1) (X 2))=S ((substitute3 Q (-X 0) (-X 1) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change (substitute3 f (-X 0) (-X 1) (X 2))=S ((substitute3 f (-X 0) (-X 1) (X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]
  · change -(substitute3 f (-X 0) (-X 1) (-X 2))=S (-(substitute3 f (-X 0) (-X 1) (-X 2)))
    simp only [S_substitute,map_neg]
    simp only [S, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs]

/-- The full table obeys the literal cycle permutation coefficient equation. -/
theorem seedValue_cycle {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (hc : C f=f) (hs : S f=f) (r : Covector) :
    seedValue f P Q (cycleRow r)=C (seedValue f P Q r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=C (0)
    simp only [map_zero]
  · change (substitute3 P (X 0) (X 1) (X 2))=C ((substitute3 P (X 2) (X 0) (X 1)))
    simp only [C_substitute]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 P (-X 0) (X 1) (X 2))=C (-(substitute3 P (-X 2) (X 0) (X 1)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 P (X 2) (X 0) (X 1))=C ((substitute3 P (X 1) (X 0) (X 2)))
    simp only [C_substitute]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_swap h]
  · change (substitute3 Q (X 0) (X 2) (X 1))=C ((substitute3 Q (X 1) (X 2) (X 0)))
    simp only [C_substitute]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change -(substitute3 Q (-X 0) (X 2) (X 1))=C (-(substitute3 Q (X 1) (-X 2) (X 0)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change -(substitute3 P (-X 2) (X 0) (X 1))=C (-(substitute3 P (-X 1) (X 0) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_swap h]
  · change -(substitute3 Q (X 0) (-X 2) (X 1))=C (-(substitute3 Q (-X 1) (X 2) (X 0)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change (substitute3 Q (-X 0) (-X 2) (X 1))=C ((substitute3 Q (-X 1) (-X 2) (X 0)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change (substitute3 P (X 1) (X 0) (X 2))=C ((substitute3 P (X 0) (X 1) (X 2)))
    simp only [C_substitute]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_swap h]
  · change (substitute3 Q (X 0) (X 1) (X 2))=C ((substitute3 Q (X 0) (X 2) (X 1)))
    simp only [C_substitute]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change -(substitute3 Q (-X 0) (X 1) (X 2))=C (-(substitute3 Q (X 0) (-X 2) (X 1)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change (substitute3 Q (X 1) (X 2) (X 0))=C ((substitute3 Q (X 0) (X 1) (X 2)))
    simp only [C_substitute]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 f (X 0) (X 1) (X 2))=C ((substitute3 f (X 0) (X 1) (X 2)))
    simp only [C_substitute]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]
  · change -(substitute3 f (-X 0) (X 1) (X 2))=C (-(substitute3 f (X 0) (X 1) (-X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]
  · change -(substitute3 Q (X 1) (-X 2) (X 0))=C (-(substitute3 Q (X 0) (-X 1) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 f (X 0) (X 1) (-X 2))=C (-(substitute3 f (X 0) (-X 1) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]
  · change (substitute3 f (-X 0) (X 1) (-X 2))=C ((substitute3 f (X 0) (-X 1) (-X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]
  · change -(substitute3 P (-X 1) (X 0) (X 2))=C (-(substitute3 P (-X 0) (X 1) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_swap h]
  · change -(substitute3 Q (X 0) (-X 1) (X 2))=C (-(substitute3 Q (-X 0) (X 2) (X 1)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change (substitute3 Q (-X 0) (-X 1) (X 2))=C ((substitute3 Q (-X 0) (-X 2) (X 1)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_swap h]
  · change -(substitute3 Q (-X 1) (X 2) (X 0))=C (-(substitute3 Q (-X 0) (X 1) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 f (X 0) (-X 1) (X 2))=C (-(substitute3 f (-X 0) (X 1) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]
  · change (substitute3 f (-X 0) (-X 1) (X 2))=C ((substitute3 f (-X 0) (X 1) (-X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]
  · change (substitute3 Q (-X 1) (-X 2) (X 0))=C ((substitute3 Q (-X 0) (-X 1) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 f (X 0) (-X 1) (-X 2))=C ((substitute3 f (-X 0) (-X 1) (X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]
  · change -(substitute3 f (-X 0) (-X 1) (-X 2))=C (-(substitute3 f (-X 0) (-X 1) (-X 2)))
    simp only [C_substitute,map_neg]
    simp only [C, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, symmetric_substitute3_swap hs, symmetric_substitute3_swap_last hc hs]

end TernaryPoly.OrdinarySeedEquivariance
